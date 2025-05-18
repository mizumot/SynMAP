from flask import Flask, render_template, request, session, send_file
from docx import Document
import os
import webbrowser
from threading import Timer
import pandas as pd
import spacy
import time
import io
from groq import Groq
import difflib
import re
import unicodedata
import numpy as np


app = Flask(__name__)

app.secret_key = 'QyS4YxF3sv8fjN0E-Lw42N9kjyZGoWHJc-rQxH9N1IU'

nlp = spacy.load('en_core_web_md')
nlp.max_length = 10000000

def load_api_key(file_path):
    try:
        with open(file_path, 'r') as file:
            return file.read().strip() 
    except FileNotFoundError:
        raise FileNotFoundError(f"API key file not found: {file_path}")
    except Exception as e:
        raise Exception(f"An error occurred while reading the API key: {str(e)}")

API_KEY_FILE = './API.txt'
API = load_api_key(API_KEY_FILE)

def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in {'txt', 'docx', 'doc'}


def open_browser():
    webbrowser.open_new('http://127.0.0.1:5000/')


def normalize_text(text):
    text = re.sub(r"^\s+", "", text)
    text = re.sub(r"\s\s+", " ", text)
    text = text.replace("’", "'")
    text = text.replace("‘", "'")
    text = text.replace("“", '"')
    text = text.replace("”", '"')
    text = text.replace("‐", "-")
    text = text.replace("？", "?")
    text = re.sub(r'[^\x00-\x7F]+', '', text)
    return text


def sanitize_filename(filename):
    normalized = unicodedata.normalize('NFC', filename).strip()
    sanitized = re.sub(r'[^\w.\-()]', '_', normalized)
    return sanitized


def safe_division(n, d):
    return n / d if d else 0


def read_file(file_stream, filename):
    try:
        ext = os.path.splitext(filename)[1].lower()
        if ext == '.txt':
            content = file_stream.read().decode('utf-8')
        elif ext == '.docx':
            document = Document(file_stream)
            content = "\n".join([para.text for para in document.paragraphs])
        else:
            content = ""
            print("Unsupported file extension.")
        return content
    except Exception as e:
        print(f"Error reading file: {str(e)}")
        return ""


def extract_t_units(text):
    doc = nlp(text)
    t_units = []
    current_unit = []
    fanboys = ["and", "nor", "but", "or", "yet", "so"]
    conjunctive_adverbs = ["consequently", "therefore", "however", "moreover", "furthermore", "nevertheless", "thus", "hence", "still", "instead", "otherwise", "likewise", "rather", "accordingly", "besides", "alternatively"]
    
    def is_independent_clause(span):
        has_subject = any(token.dep_ in ["nsubj", "nsubjpass"] for token in span)
        has_verb = any(token.pos_ in ["VERB", "AUX"] for token in span)
        return has_subject and has_verb
    
    def shares_same_subject(token):
        if token.dep_ == "conj" and token.head.pos_ == "VERB":
            head_verb = token.head
            for child in head_verb.children:
                if child.dep_ == "nsubj":
                    return True
        return False
    
    def find_next_clause_start(i):
        j = i
        while j < len(doc) and (doc[j].text.lower() in conjunctive_adverbs or
                               doc[j].text in [",", ";"]):
            j += 1
        return j
    
    def should_split_and(token, i):
        if token.text == ";" or (token.text.lower() in conjunctive_adverbs and i > 0 and doc[i-1].text in [";", ","]):
            next_idx = find_next_clause_start(i + 1)
            if next_idx < len(doc):
                next_clause = doc[next_idx:]
                return is_independent_clause(next_clause)
            return False
            
        if token.text.lower() in fanboys and i + 1 < len(doc):
            next_token = doc[i + 1]
            
            if i > 0:
                prev_token = doc[i-1]
                if (prev_token.dep_ == "relcl" or 
                    (prev_token.dep_ == "nsubj" and prev_token.text.lower() == "who") or 
                    token.head.dep_ == "relcl"):
                    return False
            
            if token.dep_ == "cc":
                head = token.head
                if head.pos_ in ["ADJ", "NOUN"]:
                    return False
                if head.dep_ in ["prep", "pobj"] and any(t.dep_ == "prep" for t in doc[i+1:i+3]):
                    return False
                if head.tag_ in ["VBG", "TO", "NN", "NNS"]:
                    return False
                if head.dep_ in ["pcomp", "conj", "dobj", "relcl", "amod", "compound"]:
                    return False
                    
                if i > 0 and i + 2 < len(doc):
                    prev_pos = doc[i-1].pos_
                    next_pos = doc[i+1].pos_
                    if (prev_pos in ["PROPN", "NOUN", "PRON"] and 
                        next_pos in ["PROPN", "NOUN"]):
                        return False
            
            j = i + 1
            while j < len(doc) and doc[j].pos_ not in ["VERB", "AUX", "NOUN", "PRON"]:
                j += 1
    
            if j < len(doc):
                next_verb_or_noun = doc[j]
                
                if next_verb_or_noun.dep_ == "conj":
                    if (next_verb_or_noun.pos_ == "ADJ" or 
                        next_verb_or_noun.head.pos_ == "ADJ" or
                        next_verb_or_noun.pos_ == "PROPN" or
                        next_verb_or_noun.head.pos_ == "PROPN"):
                        return False
                    return False
                
                if any(t.dep_ in ["compound", "amod"] for t in next_verb_or_noun.children):
                    return False
                
                if any(t.dep_ == "xcomp" for t in next_verb_or_noun.children):
                    return False
                
                if next_verb_or_noun.dep_ == "relcl" or (j > 0 and doc[j-1].text.lower() == "who"):
                    return False
                
                if next_verb_or_noun.dep_ in ["nsubj", "nsubjpass"]:
                    if any(t.dep_ == "relcl" for t in doc[i:j+1]):
                        return False
                    if i > 0 and doc[i-1].dep_ in ["nsubj", "nsubjpass"]:
                        return False
                    return True
                
                next_clause = doc[j:]
                return is_independent_clause(next_clause)
    
        return False
    
    split_indices = [0]
    split_pairs = []
    
    for i, token in enumerate(doc):
        if (token.text == ";" or 
            (token.text.lower() in conjunctive_adverbs and i > 0 and doc[i-1].text in [";", ","]) or
            token.text.lower() in fanboys):
            
            if i < len(doc) - 1:
                if should_split_and(token, i):
                    if token.text == ";":
                        split_pairs.append((split_indices[-1], i))
                        split_indices.append(i)
                    else:
                        if i > 0 and doc[i-1].text == ";":
                            split_pairs.append((split_indices[-1], i-1))
                            split_indices.append(i-1)
                        else:
                            split_pairs.append((split_indices[-1], i))
                            split_indices.append(i)
    
    split_pairs.append((split_indices[-1], len(doc)))
    
    for start, end in split_pairs:
        unit_text = ''.join(doc[j].text_with_ws for j in range(start, end))
        if unit_text.strip():
            t_units.append(unit_text.strip())
    
    return t_units


def merge_punctuation(lst):
    if len(lst) < 2:
        return lst
    last_element = lst[-1].strip()
    if last_element in [".", ",", "!", "?", '"', "'"]:
        lst[-2] = lst[-2].rstrip() + last_element
        lst.pop()
    return lst


def is_permissive_construction(token):
    """Returns True if the token is part of a permissive or causative construction."""
    if token.dep_ in ["ccomp", "xcomp"] and token.head.pos_ == "VERB":
        if token.head.lemma_ in ["allow", "let", "help", "make", "have", "get", "want"]:
            return True
        if token.head.dep_ in ["ROOT", "ccomp", "xcomp"]:
            return True
    return False


def extract_verbs(doc):
    clause_verbs = []

    for token in doc:
        if token.dep_ in ["xcomp", "amod"] and token.tag_ == "VBG":
            continue

        if token.pos_ in ["VERB", "AUX"] and token.dep_ not in ["aux"]:
            if any(child.dep_ == "aux" and child.pos_ == "PART" and child.text == "to" for child in token.children):
                continue

            if token.tag_ == "VBG" and token.dep_ not in ["advcl", "acl"]:
                continue

            passive = any(child.dep_ == "auxpass" for child in token.children)
            active = any(child.dep_ in ["nsubj", "csubj", "nsubjpass", "expl"] for child in token.children)

            if active or token.dep_ == "ROOT" or passive or token.dep_ == "advcl" or token.dep_ == "acl":
                clause_verbs.append(token)

        if token.dep_ == "relcl" and token.head.pos_ == "NOUN":
            if token not in clause_verbs:
                clause_verbs.append(token)

    return clause_verbs


def extract_clauses_using_verbs(doc, clause_verbs, extracted_clauses):
    clauses = []
    skip_until = -1

    for verb in clause_verbs:
        clause_tokens = list(verb.subtree)

        if verb.dep_ == "conj" and verb.head.pos_ == "VERB":
            for child in verb.head.children:
                if child.dep_ == "cc" and child.pos_ == "CCONJ":
                    clause_tokens = [child] + clause_tokens
                    break

        if clause_tokens[-1].i + 1 < len(doc) and doc[clause_tokens[-1].i + 1].text in [",", ";", "."]:
            clause_tokens.append(doc[clause_tokens[-1].i + 1])
            skip_until = clause_tokens[-1].i

        clause_text = "".join([t.text_with_ws for t in clause_tokens]).strip()
        
        if clause_text not in extracted_clauses:
            clauses.append(clause_text)

    return clauses


def refine_clauses(clauses):
    clauses_refined = [re.sub(r'\s+([,.;?!])', r'\1', clause).strip() for clause in clauses]

    for i in range(len(clauses_refined)):
        clauses_refined[i] = re.sub(r"\b(\w+)\s+n\s*['’]t", r"\1n't", clauses_refined[i])
        clauses_refined[i] = re.sub(r"\b(I|you|we|they|he|she|it)\s+['’](m|ve|re|d|ll|s)", r"\1'\2", clauses_refined[i])

    refined_clauses = []
    for sentence in clauses_refined:
        sentence = sentence.replace(" ’s", "’s").replace(" 's", "'s").replace(" ’", "'").replace(" '", "'")
        sentence = sentence.replace('“ ', '“').replace(' ”', '”').replace('( ', '(').replace(' )', ')')
        sentence = sentence.replace(' - ', '-')
        refined_clauses.append(sentence)

    return refined_clauses


def add_missing_part(text, output):
    if output:
        first_output = output[0].replace(' ,', ',')
        if first_output in text:
            missing_part = text[:text.index(first_output)].strip()
            output[0] = missing_part + ' ' + output[0].rstrip()

    return output


def compare_and_refine(list_of_sentences):
    refined_list = []
    refined_list.append(list_of_sentences[0].strip())
    
    for i in range(1, len(list_of_sentences)):
        current_sentence = list_of_sentences[i].strip()
        prev_sentence = refined_list[-1]
        
        if current_sentence == prev_sentence:
            continue
            
        if prev_sentence in current_sentence:
            remaining_part = current_sentence[current_sentence.index(prev_sentence) + len(prev_sentence):].strip()
            if remaining_part:
                refined_list.append(remaining_part)
                
        elif current_sentence in prev_sentence:
            start_idx = prev_sentence.index(current_sentence)
            prefix = prev_sentence[:start_idx].strip()
            if prefix:
                refined_list[-1] = prefix
            refined_list.append(current_sentence)
            
        else:
            prev_words = prev_sentence.split()
            current_words = current_sentence.split()
            
            if (len(prev_words) >= 1 and len(current_words) >= 1 and 
                prev_words[-1] == current_words[0]):
                refined_list.append(' '.join(current_words[1:]))
            else:
                refined_list.append(current_sentence)
    
    return refined_list


def process_all_sentences(clauses_only):
    results = []
    for sentence_list in clauses_only:
        refined = compare_and_refine(sentence_list)
        results.append(refined)
    return results


def clausal_complexity(token, feature_dict):
    if token.pos_ == "VERB":
        if token.dep_ != "aux":
            feature_dict["all_clauses"] += 1
            deps = [child.dep_ for child in token.children]
            if "nsubj" in deps or "nsubjpass" in deps:
                feature_dict["finite_clause"] += 1
                if token.dep_ in ["ROOT", "conj"]:
                    feature_dict["finite_ind_clause"] += 1
                else:
                    feature_dict["finite_dep_clause"] += 1
                if token.dep_ == "ccomp":
                    feature_dict["finite_compl_clause"] += 1
                if token.dep_ == "relcl":
                    feature_dict["finite_relative_clause"] += 1
            else:
                feature_dict["nonfinite_clause"] += 1
            feature_dict["vp_deps"] += len(deps)


def calculate_vp_deps(text):
    doc = nlp(text)
    vd_dict = {"vp_deps": 0, "all_clauses": 0, "finite_clause": 0, "finite_ind_clause": 0, 
                    "finite_dep_clause": 0, "finite_compl_clause": 0, "finite_relative_clause": 0, "nonfinite_clause": 0}

    for token in doc:
        if token.pos_ == 'VERB':
            clausal_complexity(token, vd_dict)

    return vd_dict


def noun_phrase_complexity(token, nominal_dict):
    if token.pos_ == "NOUN":  # only consider common nouns (exclude pronouns and proper nouns)
        nominal_dict["np"] += 1
        deps = [child.dep_ for child in token.children]
        nominal_dict["np_deps"] += len(deps)
        for x in deps:
            if x == "relcl":
                nominal_dict["relcl_dep"] += 1
            if x == "amod":
                nominal_dict["amod_dep"] += 1
            if x == "det":
                nominal_dict["det_dep"] += 1
            if x == "prep":
                nominal_dict["prep_dep"] += 1
            if x == "poss":
                nominal_dict["poss_dep"] += 1
            if x == "cc":
                nominal_dict["cc_dep"] += 1


def calculate_nominal_deps(text):
    doc = nlp(text)
    nominal_dict = {"np": 0, "np_deps": 0, "relcl_dep": 0, "amod_dep": 0, "det_dep": 0, "prep_dep": 0, "poss_dep": 0, "cc_dep": 0}

    for token in doc:
        noun_phrase_complexity(token, nominal_dict)

    return nominal_dict
   

def calculate_errors(original, corrected):
    original_words = original.split()
    corrected_words = corrected.split()

    matcher = difflib.SequenceMatcher(None, original_words, corrected_words)
    errors = 0
    highlighted_original = []
    highlighted_corrected = []

    for opcode in matcher.get_opcodes():
        tag, i1, i2, j1, j2 = opcode
        if tag == 'equal':
            highlighted_original.extend(original_words[i1:i2])
            highlighted_corrected.extend(corrected_words[j1:j2])
        elif tag == 'replace':
            highlighted_original.append('<strong>{}</strong>'.format(' '.join(original_words[i1:i2])))
            highlighted_corrected.append('<strong>{}</strong>'.format(' '.join(corrected_words[j1:j2])))
            errors += 1

        elif tag == 'insert':
            highlighted_corrected.append('<strong>{}</strong>'.format(' '.join(corrected_words[j1:j2])))
            errors += 1
        elif tag == 'delete':
            highlighted_original.append('<strong>{}</strong>'.format(' '.join(original_words[i1:i2])))
            errors += 1

    return errors, ' '.join(highlighted_original), ' '.join(highlighted_corrected)


def correct_sentences(data):
    client = Groq(api_key=API)
    prompt = "Reply with a corrected version of the input sentence with all grammatical, spelling, and punctuation errors fixed. Be strict about the possible errors. If there are no errors, reply with a copy of the original sentence. Please do not add any unnecessary explanations."

    for index, row in data.iterrows():
        text = row['Sentence']
        chat_completion = client.chat.completions.create(
            messages=[
                {"role": "system", "content": prompt},
                {"role": "user", "content": text}
            ],
            model="llama-3.3-70b-versatile",
            temperature=0,       
        )
        response = chat_completion.choices[0].message.content

        error_count, original_highlighted, corrected_highlighted = calculate_errors(text, response)

        data.loc[index, 'Corrected'] = response
        data.loc[index, 'Highlighted Original'] = original_highlighted
        data.loc[index, 'Highlighted Corrected'] = corrected_highlighted
        data.loc[index, 'Error Counts'] = error_count

        #time.sleep(1)

    return data


def check_error_in_t_units(corrected_list, t_units_list):
    error_report = []
    t_units_counts = []
    error_free_t_unit = []
    
    for i, t_units in enumerate(t_units_list):
        corrected_sentence = corrected_list[i]
        t_unit_errors = []
        no_error_count = 0
        
        for t_unit in t_units:
            if t_unit.strip() not in corrected_sentence:
                t_unit_errors.append((t_unit, "Error"))
            else:
                t_unit_errors.append((t_unit, "No Error"))
                no_error_count += 1
        
        error_report.append(t_unit_errors)
        t_units_counts.append(len(t_units))
        error_free_t_unit.append(no_error_count)

    return error_report, t_units_counts, error_free_t_unit


def check_errors_in_t_units_and_clauses(corrected_list, t_units_list, clauses_refined):
    t_units_counts = []
    clauses_counts = []
    error_free_t_unit = []
    error_free_clause = []

    for i in range(len(corrected_list)):
        corrected_sentence = corrected_list[i]

        t_units = t_units_list[i]
        t_unit_errors = []
        no_error_t_units_count = 0

        for t_unit in t_units:
            if t_unit.strip() not in corrected_sentence:
                t_unit_errors.append((t_unit, "Error"))
            else:
                t_unit_errors.append((t_unit, "No Error"))
                no_error_t_units_count += 1

        t_units_counts.append(len(t_units))
        error_free_t_unit.append(no_error_t_units_count)

        clauses = clauses_refined[i]
        clause_errors = []
        no_error_clauses_count = 0

        for clause in clauses:
            if clause.strip() not in corrected_sentence:
                clause_errors.append((clause, "Error"))
            else:
                clause_errors.append((clause, "No Error"))
                no_error_clauses_count += 1

        clauses_counts.append(len(clauses))
        error_free_clause.append(no_error_clauses_count)

    return {
        't_units_counts': t_units_counts,
        'clauses_counts': clauses_counts,
        'error_free_t_unit': error_free_t_unit,
        'error_free_clause': error_free_clause
    }


def process_hyphenated_tokens(tokens):
    """
    Helper function to process tokens and handle hyphenated words.
    Works with any iterable of tokens that have a 'text' attribute.
    
    Args:
        tokens: Iterable of tokens with 'text' attribute
        
    Returns:
        str: Processed text with hyphenated words properly joined
    """
    processed_tokens = []
    tokens = list(tokens)  # Convert to list for indexing
    i = 0
    while i < len(tokens):
        if (i + 2 < len(tokens) and 
            tokens[i+1].text == '-'):
            # Combine hyphenated words
            processed_tokens.append(
                tokens[i].text + 
                tokens[i+1].text + 
                tokens[i+2].text
            )
            i += 3
        else:
            processed_tokens.append(tokens[i].text)
            i += 1
    return " ".join(processed_tokens)


# (1) Dependent phrase (nonclausal)	
# - Compound nouns: The **garden tools** need to be cleaned.
# - Adjectives: An **entire team** worked on the project. 
# - Prepositional phrases: The book **on the table** belongs to Sarah. 

def extract_dependent_phrases(sent):
    """
    Extracts dependent phrases (compound nouns, adjectives, prepositional phrases)
    from a sentence.
    """
    nouns = []
    prepositions = []
    adjectives = []
    
    # 処理済みのトークンを追跡
    processed_tokens = set()
    
    for token in sent:
        # Adjectives (amodを持つ場合の特別処理)
        if token.dep_ == 'amod' and token.i not in processed_tokens:
            # ハイフンケースの確認
            if (token.i + 2 < len(token.doc) and 
                token.doc[token.i + 1].text == '-' and
                token.doc[token.i + 2].dep_ == 'compound'):
                # 最終的な名詞（job）を見つける
                final_noun = token.doc[token.i + 2].head
                adj_tokens = [token, token.doc[token.i + 1], token.doc[token.i + 2], final_noun]
                adj_text = process_hyphenated_tokens(adj_tokens[:3]) + " " + final_noun.text
                adjectives.append(adj_text)
                # これらのトークンを処理済みとしてマーク
                processed_tokens.update([t.i for t in adj_tokens])
            else:
                adjectives.append(process_hyphenated_tokens([token, token.head]))
                processed_tokens.update([token.i, token.head.i])
        
        # Compound nouns
        if (token.dep_ == 'compound' and token.head.pos_ == 'NOUN' and 
            token.i not in processed_tokens and token.head.i not in processed_tokens):
            # ハイフンの前後のトークンでない場合のみ処理
            prev_token = token.doc[token.i - 1] if token.i > 0 else None
            if not (prev_token and prev_token.dep_ == 'amod'):
                nouns.append(process_hyphenated_tokens([token, token.head]))
                processed_tokens.update([token.i, token.head.i])
        
        # Prepositional phrases
        if token.pos_ == 'ADP' and token.dep_ == 'prep':
            # Skip if this is part of 'in order to'
            next_tokens = [token.doc[i] for i in range(token.i, min(token.i + 3, len(token.doc)))]
            is_in_order_to = (len(next_tokens) >= 3 and
                           next_tokens[0].text.lower() == 'in' and
                           next_tokens[1].text.lower() == 'order' and
                           next_tokens[2].text.lower() == 'to')
            
            if not is_in_order_to:
                contains_relative = False
                for child in token.children:
                    if child.tag_ in {'WP', 'WDT'}:
                        contains_relative = True
                        break
                
                if not contains_relative:
                    prep_tokens = [token]
                    for child in token.children:
                        if child.dep_ == 'pobj':
                            subtree = list(child.subtree)
                            subtree.sort(key=lambda x: x.i)
                            prep_tokens.extend(subtree)
                    
                    if len(prep_tokens) > 1:
                        prep_phrase = process_hyphenated_tokens(prep_tokens)
                        prepositions.append(prep_phrase)
    
    return {
        "compound_nouns": nouns,
        "prepositions": prepositions,
        "adjectives": adjectives
    }


# (2) Finite noun modifier clauses (relative clauses)
# - Noun + that relative clauses: The car **that is parked** outside is mine. 
# - Noun + wh relative clauses: The woman **who is speaking** is my teacher. 

def extract_relative_clauses(sent):
    """
    Extracts relative clauses (that-clauses and wh-clauses) from a sentence.
    """
    that_clauses = []
    wh_clauses = []
    
    for token in sent:
        if token.dep_ == 'relcl':
            clause_tokens = []
            rel_pronoun = None
            prep = None
            
            for child in token.children:
                if child.tag_ in {'WP', 'WDT', 'WRB'}:
                    rel_pronoun = child
                    break
                elif child.dep_ == 'mark' and child.text.lower() == 'that':
                    rel_pronoun = child
                    break
                elif child.dep_ == 'prep':
                    for prep_child in child.children:
                        if prep_child.tag_ in {'WP', 'WDT', 'WRB'}:
                            prep = child
                            rel_pronoun = prep_child
                            break
                    if rel_pronoun:
                        break
            
            if rel_pronoun:
                subtree = list(token.subtree)
                subtree.sort(key=lambda x: x.i)
                clause = process_hyphenated_tokens(subtree)
                
                if rel_pronoun.text.lower() == 'that':
                    that_clauses.append(clause)
                else:
                    wh_clauses.append(clause)
    
    return {
        "that_relative_clauses": that_clauses,
        "wh_relative_clauses": wh_clauses
    }

# (3) Finite complement clauses
# - Verb + that clauses: He said **that the project is complete**.
# - Verb + wh clauses: I don’t know **where they are going**. 
# - Adjective + that clauses: It is unfortunate **that she missed the event**. 
# - Noun + that clauses: His belief **that hard work pays off** motivates him. 

def extract_complement_clauses(sent):
    """
    Extracts finite complement clauses with special handling for adjective complements
    """
    verb_that_clauses = []
    verb_wh_clauses = []
    adj_that_clauses = []
    noun_that_clauses = []
    
    for token in sent:
        if token.dep_ == 'ccomp':
            clause_tokens = [t for t in token.subtree]
            clause_tokens.sort(key=lambda x: x.i)
            clause = process_hyphenated_tokens(clause_tokens)
            head = token.head
            
            # Check for 'that' complementizer
            has_that = any(child.dep_ == 'mark' and child.text.lower() == 'that' 
                          for child in token.children)
            # Check for wh-word
            has_wh = any(child.tag_ in {'WRB', 'WP', 'WDT'} 
                        for child in token.children)
            
            # Check if the head is 'be' and has an adjective complement
            if has_that and head.lemma_ == "be":
                adj_comp = None
                for child in head.children:
                    if child.dep_ == "acomp" and child.pos_ == "ADJ":
                        adj_comp = child
                        break
                
                if adj_comp:
                    adj_that_clauses.append(clause)
                    continue
            
            # Handle other cases
            if has_that:
                verb_that_clauses.append(clause)
            elif has_wh:
                verb_wh_clauses.append(clause)
                
        # Noun complementation
        elif token.dep_ == 'acl' and token.head.pos_ == 'NOUN':
            if any(child.dep_ == 'mark' and child.text.lower() == 'that' 
                  for child in token.children):
                clause_tokens = [t for t in token.subtree]
                clause_tokens.sort(key=lambda x: x.i)
                clause = process_hyphenated_tokens(clause_tokens)
                noun_that_clauses.append(clause)
    
    return {
        "verb_that_clauses": verb_that_clauses,
        "verb_wh_clauses": verb_wh_clauses,
        "adj_that_clauses": adj_that_clauses,
        "noun_that_clauses": noun_that_clauses
    }


# (4) Finite adverbial clauses 
# - Conditional adverbial subordination: **If** it rains, we will stay indoors.
# - Causative adverbial subordination: **Because** she studied hard, she passed the exam.
# - Concessive adverbial subordination: **Although** it was late, we continued working.
# - Temporal adverbial subordination: **When** I speak in English, I feel my personality changes.
# - Other adverbial subordination: She moved here **so that** she could be closer to her family. / **Whenever** he calls, she feels happy.

def extract_adverbial_clauses(sent, *, previous_extractions=None):
    """
    Extracts finite adverbial clauses marked by subordinating conjunctions,
    excluding those already captured in other categories.
    
    Args:
        sent: The spaCy sentence
        previous_extractions: Dictionary containing results from other extraction functions
    """
    if previous_extractions is None:
        previous_extractions = {}
    
    # Collect all previously extracted phrases
    existing_phrases = set()
    for category, phrases in previous_extractions.items():
        if isinstance(phrases, list):
            existing_phrases.update(phrases)
        elif isinstance(phrases, dict):
            for subcat_phrases in phrases.values():
                existing_phrases.update(subcat_phrases)
    
    adverbial_clauses = []
    tokens = [token for token in sent]
    skip_indices = set()
    
    # First pass: detect two-word subordinating conjunctions
    i = 0
    while i < len(tokens) - 1:
        if (tokens[i].pos_ == 'SCONJ' and tokens[i].tag_ == 'IN' and tokens[i].dep_ == 'mark' and
            tokens[i+1].pos_ == 'SCONJ' and tokens[i+1].tag_ == 'IN' and tokens[i+1].dep_ == 'mark'):
            
            clause_head = tokens[i].head
            clause_tokens = [t for t in clause_head.subtree]
            clause_tokens.sort(key=lambda x: x.i)
            clause = process_hyphenated_tokens(clause_tokens)
            
            # Only add if not already extracted
            if clause not in existing_phrases:
                adverbial_clauses.append(clause)
            skip_indices.update([i, i+1])
            i += 2
        else:
            i += 1
    
    # Second pass: single-word subordinating conjunctions
    for idx, token in enumerate(tokens):
        if idx in skip_indices:
            continue
            
        if ((token.pos_ == 'SCONJ' and token.tag_ == 'IN' and token.dep_ == 'mark') or
            (token.pos_ == 'SCONJ' and token.tag_ == 'WRB' and token.dep_ == 'advmod')):
            
            clause_head = token.head
            clause_tokens = [t for t in clause_head.subtree]
            clause_tokens.sort(key=lambda x: x.i)
            clause = process_hyphenated_tokens(clause_tokens)
            
            # Only add if not already extracted
            if clause not in existing_phrases:
                adverbial_clauses.append(clause)
    
    return {
        "adverbial_clauses": adverbial_clauses
    }


# (5) Nonfinite noun modifier clauses
# 現在分詞と過去分詞による名詞修飾節
# - Noun + present participial: The students **taking the exam** are nervous.
# - Noun + past participial clauses: The documents **submitted yesterday** need a signature.

def extract_nonfinite_modifiers(sent):
    """
    Extracts nonfinite noun modifier clauses:
    - Present participial clauses (Verb-ing)
    - Past participial clauses (Verb-ed/en)
    """
    present_participials = []
    past_participials = []
    
    for token in sent:
        # For participles modifying nouns (acl dependency)
        if token.dep_ == 'acl':
            # Get the full clause
            clause_tokens = [t for t in token.subtree]
            clause_tokens.sort(key=lambda x: x.i)
            clause = process_hyphenated_tokens(clause_tokens)
            
            # Check verb form using morphology
            if token.tag_ == 'VBG':  # Present participle
                present_participials.append(clause)
            elif token.tag_ == 'VBN':  # Past participle
                past_participials.append(clause)
    
    return {
        "present_participials": present_participials,
        "past_participials": past_participials
    }


# (6) Nonfinite complement clauses (infinitives)
# - Verb + to clauses: She decided **to take a break**. / He explained **how to use the device**.
# - Adjective + to clauses: It is important **to have various experiences**.
# - Noun + to clauses: The decision **to cancel the trip** was difficult.

def extract_infinitives(sent):
    """
    Extracts infinitive complement clauses:
    - Verb + to clauses (including how/what/etc. + to)
    - Adjective + to clauses
    - Noun + to clauses
    
    Note: 'in order to' phrases are handled by extract_adverbial_infinitives
    """
    verb_to_clauses = []
    adj_to_clauses = []
    noun_to_clauses = []
    
    for token in sent:
        # Check for both xcomp and acl dependencies
        if token.dep_ in {'xcomp', 'acl'}:
            # Look for 'to' in the clause
            has_to = False
            to_token = None
            for child in token.children:
                if child.text.lower() == 'to' and child.dep_ == 'aux':
                    has_to = True
                    to_token = child
                    break
            
            if has_to:
                # Skip if this is part of 'in order to'
                is_in_order_to = False
                if token.i >= 3:  # Make sure we have enough previous tokens to check
                    prev_tokens = [token.doc[i] for i in range(token.i - 3, token.i)]
                    if (prev_tokens[0].text.lower() == 'in' and
                        prev_tokens[1].text.lower() == 'order' and
                        prev_tokens[2].text.lower() == 'to'):
                        is_in_order_to = True
                
                if not is_in_order_to:
                    # Get the clause
                    clause_tokens = [t for t in token.subtree]
                    clause_tokens.sort(key=lambda x: x.i)
                    clause = process_hyphenated_tokens(clause_tokens)
                    
                    # Get the head word
                    head = token.head
                    
                    # Classify based on the dependency and head's POS
                    if token.dep_ == 'acl' and head.pos_ == 'NOUN':
                        noun_to_clauses.append(clause)
                    elif head.pos_ == 'VERB':
                        verb_to_clauses.append(clause)
                    elif head.pos_ == 'ADJ':
                        adj_to_clauses.append(clause)
                    elif head.lemma_ == 'be' and any(c.pos_ == 'ADJ' for c in head.children):
                        # Handle "It is ADJ to..." cases
                        adj_to_clauses.append(clause)
    
    return {
        "verb_to_clauses": verb_to_clauses,
        "adj_to_clauses": adj_to_clauses,
        "noun_to_clauses": noun_to_clauses
    }


# (7) Nonfinite adverbial clauses (infinitives)
# - To adverbial clauses: **To improve his health**, John started jogging every morning.

def extract_adverbial_infinitives(sent, *, previous_extractions=None):
    """
    Extracts nonfinite adverbial clauses (to-infinitives) that function as adverbials,
    excluding those already captured in other categories.
    
    Args:
        sent: The spaCy sentence
        previous_extractions: Dictionary containing results from other extraction functions
    
    Returns:
        Dictionary containing non-duplicate adverbial infinitives
    """
    if previous_extractions is None:
        previous_extractions = {}
    
    # Collect all previously extracted phrases
    existing_phrases = set()
    for category, phrases in previous_extractions.items():
        if isinstance(phrases, list):
            existing_phrases.update(phrases)
        elif isinstance(phrases, dict):
            for subcat_phrases in phrases.values():
                existing_phrases.update(subcat_phrases)
    
    adverbial_infinitives = []
    
    for token in sent:
        # Case 1: Simple 'to' infinitive as adverbial
        if (token.text.lower() == 'to' and 
            token.dep_ == 'aux' and 
            (token.head.dep_ in {'advcl', 'acl'} or
             (token.head.dep_ == 'xcomp' and token.head.head.pos_ != 'NOUN'))):
            
            # Skip if this is part of 'in order to'
            prev_tokens = [token.doc[i] for i in range(max(0, token.i - 2), token.i)]
            if not (len(prev_tokens) == 2 and
                   prev_tokens[0].text.lower() == 'in' and
                   prev_tokens[1].text.lower() == 'order'):
                
                clause_tokens = [t for t in token.head.subtree]
                clause_tokens.sort(key=lambda x: x.i)
                clause = process_hyphenated_tokens(clause_tokens)
                
                # Only add if not already extracted
                if clause not in existing_phrases:
                    adverbial_infinitives.append(clause)
            
        # Case 2: 'in order to' pattern
        elif (token.text.lower() == 'in' and 
              token.i + 2 < len(token.doc) and
              token.doc[token.i + 1].text.lower() == 'order' and
              token.doc[token.i + 2].text.lower() == 'to'):
            
            inf_verb = token.doc[token.i + 2].head
            if inf_verb.dep_ in {'advcl', 'acl', 'xcomp'}:
                clause_tokens = [token, token.doc[token.i + 1], token.doc[token.i + 2]]
                clause_tokens.extend(t for t in inf_verb.subtree if t not in clause_tokens)
                clause_tokens.sort(key=lambda x: x.i)
                clause = process_hyphenated_tokens(clause_tokens)
                
                # Only add if not already extracted
                if clause not in existing_phrases:
                    adverbial_infinitives.append(clause)
    
    return {
        "adverbial_infinitives": adverbial_infinitives
    }


def process_text(text):
    """
    Processes text and extracts various grammatical structures.
    Returns a list of dictionaries containing analysis results for each sentence.
    """
    nlp = spacy.load("en_core_web_md")
    #nlp = spacy.load('en_core_web_sm') #MacBook Pro用（変更する）
    doc = nlp(text)
    results = []
    
    for sent in doc.sents:
        # Create a dictionary to store all extractions
        all_extractions = {}
        
        # Extract structures in order
        dependent_phrases = extract_dependent_phrases(sent)
        all_extractions.update(dependent_phrases)
        
        relative_clauses = extract_relative_clauses(sent)
        all_extractions.update(relative_clauses)
        
        complement_clauses = extract_complement_clauses(sent)
        all_extractions.update(complement_clauses)
        
        nonfinite_modifiers = extract_nonfinite_modifiers(sent)
        all_extractions.update(nonfinite_modifiers)
        
        infinitives = extract_infinitives(sent)
        all_extractions.update(infinitives)
        
        # Extract adverbial clauses with previous extractions
        adverbial_clauses = extract_adverbial_clauses(sent, previous_extractions=all_extractions)
        all_extractions.update(adverbial_clauses)
        
        # Extract adverbial infinitives with all previous extractions
        adverbial_infinitives = extract_adverbial_infinitives(sent, previous_extractions=all_extractions)
        all_extractions.update(adverbial_infinitives)
        
        # Combine all results
        result = {
            "sentence": sent.text.strip(),
            **all_extractions
        }
        results.append(result)
    
    return results

def categorize_sentence_results(results):
    """
    Reorganizes extraction results into 7 major categories for each sentence.
    
    Args:
        results: List of dictionaries containing detailed extraction results
    
    Returns:
        List of dictionaries, each containing sentence and its 7 major categories
    """
    categorized_sentences = []
    
    for result in results:
        # 各文のカテゴリーを初期化
        categories = {
            "sentence": result["sentence"],
            "dependent_phrases": [],
            "finite_noun_modifier_clauses": [],
            "finite_complement_clauses": [],
            "finite_adverbial_clauses": [],
            "nonfinite_noun_modifier_clauses": [],
            "nonfinite_complement_clauses": [],
            "nonfinite_adverbial_clauses": []
        }
        
        # 1. Dependent Phrases
        if "compound_nouns" in result:
            categories["dependent_phrases"].extend(result["compound_nouns"])
        if "adjectives" in result:
            categories["dependent_phrases"].extend(result["adjectives"])
        if "prepositions" in result:
            categories["dependent_phrases"].extend(result["prepositions"])
        
        # 2. Finite Noun Modifier Clauses
        if "that_relative_clauses" in result:
            categories["finite_noun_modifier_clauses"].extend(result["that_relative_clauses"])
        if "wh_relative_clauses" in result:
            categories["finite_noun_modifier_clauses"].extend(result["wh_relative_clauses"])
        
        # 3. Finite Complement Clauses
        if "verb_that_clauses" in result:
            categories["finite_complement_clauses"].extend(result["verb_that_clauses"])
        if "verb_wh_clauses" in result:
            categories["finite_complement_clauses"].extend(result["verb_wh_clauses"])
        if "adj_that_clauses" in result:
            categories["finite_complement_clauses"].extend(result["adj_that_clauses"])
        if "noun_that_clauses" in result:
            categories["finite_complement_clauses"].extend(result["noun_that_clauses"])
        
        # 4. Finite Adverbial Clauses
        if "adverbial_clauses" in result:
            categories["finite_adverbial_clauses"].extend(result["adverbial_clauses"])
        
        # 5. Nonfinite Noun Modifiers
        if "present_participials" in result:
            categories["nonfinite_noun_modifier_clauses"].extend(result["present_participials"])
        if "past_participials" in result:
            categories["nonfinite_noun_modifier_clauses"].extend(result["past_participials"])
        
        # 6. Nonfinite Complement Clauses
        if "verb_to_clauses" in result:
            categories["nonfinite_complement_clauses"].extend(result["verb_to_clauses"])
        if "adj_to_clauses" in result:
            categories["nonfinite_complement_clauses"].extend(result["adj_to_clauses"])
        if "noun_to_clauses" in result:
            categories["nonfinite_complement_clauses"].extend(result["noun_to_clauses"])
        
        # 7. Nonfinite Adverbial Clauses
        if "adverbial_infinitives" in result:
            categories["nonfinite_adverbial_clauses"].extend(result["adverbial_infinitives"])
        
        categorized_sentences.append(categories)
    
    return categorized_sentences


def create_analysis_dataframe(categorized_sentences):
    """
    Creates a combined analysis dataframe from categorized_sentences results.
    
    Args:
        categorized_sentences: List of dictionaries containing categorized grammatical elements
        
    Returns:
        pandas.DataFrame: Combined dataframe with frequency counts and extracted items
    """
    frequency_data = []
    extracted_items = []
    
    for categories in categorized_sentences:
        # Create frequency data dictionary
        freq = {
            'DP_freq': len(categories["dependent_phrases"]),
            'FNM_freq': len(categories["finite_noun_modifier_clauses"]),
            'FCC_freq': len(categories["finite_complement_clauses"]),
            'FAC_freq': len(categories["finite_adverbial_clauses"]),
            'NFM_freq': len(categories["nonfinite_noun_modifier_clauses"]),
            'NCC_freq': len(categories["nonfinite_complement_clauses"]),
            'NAC_freq': len(categories["nonfinite_adverbial_clauses"])
        }
        
        # Create extracted items dictionary
        items = {
            'DP_items': '; '.join(categories["dependent_phrases"]) if categories["dependent_phrases"] else '',
            'FNM_items': '; '.join(categories["finite_noun_modifier_clauses"]) if categories["finite_noun_modifier_clauses"] else '',
            'FCC_items': '; '.join(categories["finite_complement_clauses"]) if categories["finite_complement_clauses"] else '',
            'FAC_items': '; '.join(categories["finite_adverbial_clauses"]) if categories["finite_adverbial_clauses"] else '',
            'NFM_items': '; '.join(categories["nonfinite_noun_modifier_clauses"]) if categories["nonfinite_noun_modifier_clauses"] else '',
            'NCC_items': '; '.join(categories["nonfinite_complement_clauses"]) if categories["nonfinite_complement_clauses"] else '',
            'NAC_items': '; '.join(categories["nonfinite_adverbial_clauses"]) if categories["nonfinite_adverbial_clauses"] else ''
        }
        
        frequency_data.append({
            'sentence': categories["sentence"],
            **freq
        })
        
        extracted_items.append(items)
    
    # Create and combine dataframes
    freq_df = pd.DataFrame(frequency_data)
    items_df = pd.DataFrame(extracted_items)
    combined_df = pd.concat([freq_df, items_df], axis=1)
    
    return combined_df


def get_detailed_statistics(corrected_list, results):
    # 各カテゴリの統計を保持する辞書
    category_stats = {
        'DP': {'total': 0, 'error_free': 0},
        'FNM': {'total': 0, 'error_free': 0},
        'FCC': {'total': 0, 'error_free': 0},
        'FAC': {'total': 0, 'error_free': 0},
        'NFM': {'total': 0, 'error_free': 0},
        'NCC': {'total': 0, 'error_free': 0},
        'NAC': {'total': 0, 'error_free': 0}
    }
    
    # カテゴリと結果のマッピング
    category_fields = {
        'DP': ['compound_nouns', 'adjectives', 'prepositions'],
        'FNM': ['that_relative_clauses', 'wh_relative_clauses'],
        'FCC': ['verb_that_clauses', 'verb_wh_clauses', 'adj_that_clauses', 'noun_that_clauses'],
        'FAC': ['adverbial_clauses'],
        'NFM': ['present_participials', 'past_participials'],
        'NCC': ['verb_to_clauses', 'adj_to_clauses', 'noun_to_clauses'],
        'NAC': ['adverbial_infinitives']
    }

    # 各カテゴリごとにカウント
    for result, corrected in zip(results, corrected_list):
        for category, fields in category_fields.items():
            items = []
            for field in fields:
                items.extend(result[field])
            category_stats[category]['total'] += len(items)
            category_stats[category]['error_free'] += sum(1 for item in items if item.strip() in corrected)
    
    # 以下は元のコードと同じ
    df_data = {
        'Total': {},
        'Error_Free': {},
        'Error_Free_Rate': {}
    }
    
    def format_rate(rate):
        if rate == 100 or rate == 0:
            return str(int(rate))
        return f"{rate:.2f}"
    
    total_items = 0
    total_error_free = 0
    
    for category, stats in category_stats.items():
        df_data['Total'][category] = stats['total']
        df_data['Error_Free'][category] = stats['error_free']
        total_items += stats['total']
        total_error_free += stats['error_free']
        
        if stats['total'] > 0:
            rate = (stats['error_free'] / stats['total']) * 100
            df_data['Error_Free_Rate'][category] = format_rate(rate)
        else:
            df_data['Error_Free_Rate'][category] = "0"
    
    if total_items > 0:
        overall_rate = (total_error_free / total_items) * 100
        overall_rate_formatted = format_rate(overall_rate)
    else:
        overall_rate_formatted = "0"
        
    df_data['Total']['Overall'] = total_items
    df_data['Error_Free']['Overall'] = total_error_free
    df_data['Error_Free_Rate']['Overall'] = overall_rate_formatted
    
    stats_df = pd.DataFrame(df_data)
    
    return stats_df


def calculate_overall_syntactic_maturity(df, corrected_list, grammar_results):
    grammar_columns = ['DP_freq', 'FNM_freq', 'FCC_freq', 'FAC_freq', 'NFM_freq', 'NCC_freq', 'NAC_freq']
    
    # Error Free Rate の計算
    total_items = 0
    error_free_items = 0
    
    category_mapping = {
        'dependent_phrases': 'DP_freq',
        'finite_noun_modifier_clauses': 'FNM_freq',
        'finite_complement_clauses': 'FCC_freq',
        'finite_adverbial_clauses': 'FAC_freq',
        'nonfinite_noun_modifier_clauses': 'NFM_freq',
        'nonfinite_complement_clauses': 'NCC_freq',
        'nonfinite_adverbial_clauses': 'NAC_freq'
    }

    # Error Free Rate の計算
    for result, corrected in zip(grammar_results, corrected_list):
        for full_name in category_mapping.keys():
            items = result[full_name]
            total_items += len(items)
            error_free_items += sum(1 for item in items if item.strip() in corrected)
    
    error_free_rate = round((error_free_items / total_items * 100), 2) if total_items > 0 else 0.0
    normalized_error_free_rate = error_free_rate / 100  # 総合スコア計算用に0-1に正規化
    
    # 1. 全体の文法項目使用率の計算（正規化版）
    total_grammar_items = df[grammar_columns].sum().sum()
    grammar_usage_rate = min(1.0, total_grammar_items / (len(df) * len(grammar_columns)))
    
    # 2. 文法項目の多様性の計算（すでに0-1の範囲）
    used_grammar_types = (df[grammar_columns].sum() > 0).sum()
    grammar_diversity = used_grammar_types / len(grammar_columns)
    
    # 3. 文法項目の分布の均一性（エントロピー）の計算（正規化版）
    grammar_proportions = df[grammar_columns].sum() / total_grammar_items
    entropy = -np.sum(grammar_proportions * np.log2(grammar_proportions + 1e-10))
    normalized_entropy = min(1.0, entropy / np.log2(len(grammar_columns)))
    
    # 4. 総合スコアの計算 (0-1の範囲) - Error Free Rateを含む
    overall_score = (
        grammar_usage_rate * 0.25 +
        grammar_diversity * 0.25 +
        normalized_entropy * 0.25 +
        normalized_error_free_rate * 0.25
    )
    
    analysis_results = {
        'overall_syntactic_maturity': round(overall_score * 100, 2),  # パーセント表示
        'grammar_usage_rate': round(grammar_usage_rate * 100, 2),     # パーセント表示
        'grammar_diversity': round(grammar_diversity * 100, 2),       # パーセント表示
        'distribution_uniformity': round(normalized_entropy * 100, 2), # パーセント表示
        'error_free_rate': round(error_free_rate, 2),                # すでにパーセント
        'total_grammar_items': int(total_grammar_items),
        #'average_items_per_sentence': round(total_grammar_items / len(df), 2)
    }
    
    return analysis_results





def create_html_highlight(text, analysis_result, show_legend=False):
    # 文法要素ごとの色を定義
    highlight_colors = {
        'dependent_phrases': '#FFF59D',      # 薄い黄色
        
        # finite系（ピンク/パープル系統）
        'finite_noun_modifier_clauses': '#EF7070',   # 赤
        'finite_complement_clauses': '#E1BEE7', # ラベンダー
        'finite_adverbial_clauses': '#FFCDD2', # 薄い赤
        
        # nonfinite系（青系統）
        'nonfinite_noun_modifier_clauses': '#1976D2', # より濃いブルー
        'nonfinite_complement_clauses': '#4FC3F7',    # よりライトなブルー
        'nonfinite_adverbial_clauses': '#80DEEA',  # 変更
    }

    typeDescriptions = {
        'dependent_phrases':
            'Dependent Phrases (nonclausal): compound nouns, adjectives, prepositions',
        'finite_noun_modifier_clauses':
            'Finite Noun Modifier Clauses (relative clauses): that relative clauses, wh relative clauses',
        'finite_complement_clauses':
            'Finite Complement Clauses: verb that-clauses, verb wh-clauses, adj that-clauses, noun that-clauses',
        'finite_adverbial_clauses':
            'Finite Adverbial Clauses: adverbial clauses',
        'nonfinite_noun_modifier_clauses':
            'Nonfinite Noun Modifier Clauses: present participials, past participials',
        'nonfinite_complement_clauses':
            'Nonfinite Complement Clauses (infinitives): verb to-clauses, adj to-clauses, noun to-clauses',
        'nonfinite_adverbial_clauses':
            'Nonfinite Adverbial Clauses (infinitives): adverbial infinitives'
    }

    # CSSスタイルの定義
    css = """
    <style>
        .grammar-container {
            font-family: Arial, sans-serif;
            margin: 20px;
            padding: 20px;
            border: 1px solid #ddd;
            border-radius: 5px;
        }
        .sentence-container {
            margin: 10px 0;
            line-height: 1.6;
        }
        .highlight-text {
            padding: 2px 4px;
            border-radius: 3px;
        }
        .legend {
            margin-top: 20px;
            padding: 10px;
            border-top: 1px solid #eee;
        }
        .legend-item {
            display: flex;
            align-items: center;
            margin: 5px 0;
        }
        .legend-color {
            width: 20px;
            height: 20px;
            margin-right: 10px;
            border-radius: 3px;
        }
    </style>
    """

    # 前置詞句の開始位置と全範囲を記録
    preposition_starts = {}
    preposition_ranges = set()
    if 'dependent_phrases' in analysis_result and analysis_result['dependent_phrases']:
        for prep_phrase in analysis_result['dependent_phrases']:
            start = 0
            while True:
                pos = text.find(prep_phrase, start)
                if pos == -1:
                    break
                preposition_starts[pos] = prep_phrase
                preposition_ranges.update(range(pos, pos + len(prep_phrase)))
                start = pos + 1

    # 各文法要素に基づき文字位置を追跡
    spans = []
    
    # まず前置詞句を追加
    for start_pos, phrase in preposition_starts.items():
        spans.append({
            'start': start_pos,
            'end': start_pos + len(phrase),
            'type': 'dependent_phrases',
            'text': phrase
        })

    # 他の要素を処理
    for element_type, items in analysis_result.items():
        if element_type == 'sentence' or element_type == 'dependent_phrases' or not isinstance(items, list):
            continue
        for item in items:
            if item and isinstance(item, str):
                start = 0
                while True:
                    pos = text.find(item, start)
                    if pos == -1:
                        break
                    in_preposition = False
                    for prep_start, prep_phrase in preposition_starts.items():
                        if prep_start <= pos < prep_start + len(prep_phrase):
                            if pos == prep_start:
                                in_preposition = True
                            break
                    if not in_preposition:
                        # element_typeが highlight_colors に存在することを確認
                        if element_type in highlight_colors:
                            spans.append({
                                'start': pos,
                                'end': pos + len(item),
                                'type': element_type,
                                'text': item
                            })
                    start = pos + 1

    spans.sort(key=lambda x: (x['start'], x['end']))

    def create_span_html(text_segment, types):
        if not types:
            return text_segment
        # highlight_colors は関数外で定義済みの前提
        valid_types = [t for t in types if t in highlight_colors]
        if not valid_types:
            return text_segment

        def get_title(code):
            return typeDescriptions.get(code, code.replace('_', ' '))

        if len(valid_types) == 1:
            code  = valid_types[0]
            desc  = get_title(code)
            color = highlight_colors[code]
            return (
                f'<span class="highlight-text" '
                f'style="background-color: {color}" '
                f'data-toggle="tooltip" '
                f'title="{desc}">'
                f'{text_segment}'
                f'</span>'
            )
        else:
            # 2つ以上のとき：<hr> で区切った HTML を作成
            titles   = [ get_title(c) for c in valid_types ]
            # <hr> を挟んで結合
            html_tooltip = '<hr>'.join(titles)
            # 背景グラデ
            colors   = [highlight_colors[c] for c in valid_types]
            gradient = f"linear-gradient(45deg, {colors[0]} 50%, {colors[1]} 50%)"
            return (
                f'<span class="highlight-text" '
                f'style="background: {gradient}" '
                f'data-toggle="tooltip" '
                f'data-html="true" '
                f'title="{html_tooltip}">'
                f'{text_segment}'
                f'</span>'
            )

    # ── テキスト全体を span 断片に分割してハイライトを適用 ──
    result_html = []
    i = 0
    while i < len(text):
        active_spans = [span for span in spans if span['start'] <= i < span['end']]
        current_types = [span['type'] for span in active_spans]
        next_change = min(
            [span['end']   for span in active_spans if span['end'] > i] +
            [span['start'] for span in spans          if span['start'] > i] +
            [len(text)]
        )
        segment = text[i:next_change]
        result_html.append(create_span_html(segment, current_types))
        i = next_change

    highlighted_text = ''.join(result_html)

    # ── 凡例の HTML を組み立て ──
    legend_html = ''
    if show_legend:
        legend_html = '<div class="legend">'
        for element_type, color in highlight_colors.items():
            legend_html += (
                '<div class="legend-item">'
                f'  <div class="legend-color" style="background-color: {color};"></div>'
                f'  <span>{element_type.replace("_", " ")}</span>'
                '</div>'
            )
        legend_html += '</div>'

    # ── 最終出力 HTML を返す ──
    final_html = (
        (css if show_legend else '') +
        f'<div class="{"grammar-container" if show_legend else "sentence-container"}">'
        f'  <div>{highlighted_text}</div>'
        f'  {legend_html}'
        '</div>'
    )

    return final_html


def create_legend():
    """凡例のみを作成する関数"""
    highlight_colors = {
        'dependent_phrases': '#FFF59D',      # 薄い黄色
        
        # finite系（ピンク/パープル系統）
        'finite_noun_modifiers': '#EF7070',   # 赤
        'finite_complement_clauses': '#E1BEE7', # ラベンダー
        'finite_adverbial_clauses': '#FFCDD2', # 薄い赤
        
        # nonfinite系（青系統）
        'nonfinite_noun_modifier_clauses': '#1976D2', # より濃いブルー
        'nonfinite_complement_clauses': '#4FC3F7',    # よりライトなブルー
        'nonfinite_adverbial_clauses': '#80DEEA',  # 変更
    }

    css = """
    <style>
        .legend-container {
            font-family: Arial, sans-serif;
            padding: 20px;
            background: transparent;
            box-shadow: none;
            border: none;
            margin-top: 20px;
        }
        .legend {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 10px;
            padding: 10px;
            background: #ffffff;
            border-radius: 5px;
        }
        .legend-item {
            display: flex;
            align-items: center;
            font-size: 14px;
        }
        .legend-color {
            width: 20px;
            height: 20px;
            margin-right: 8px;
            border-radius: 3px;
        }
        .legend, .legend-container {
            text-transform: capitalize;
        }

    </style>
    """

    legend_html = f"""
    {css}
    <div class="legend-container">
        <div class="legend">
    """
    
    for element_type, color in highlight_colors.items():
        legend_html += f"""
            <div class="legend-item">
                <div class="legend-color" style="background-color: {color};"></div>
                <span>{element_type.replace('_', ' ')}</span>
            </div>
        """
    
    legend_html += '</div></div>'
    
    return legend_html



############################################################################################################################################

@app.route('/', methods=['POST', 'GET'])
def home():
    try:
        text = ''
        e_time = ''
        fluencytable = pd.DataFrame()
        complexitytable = pd.DataFrame()
        accuracytytable = pd.DataFrame()
        data = pd.DataFrame()
        corrected_data = pd.DataFrame()
        output_data = pd.DataFrame()
        grammar_data = pd.DataFrame()
        highlighted_sentences = []
        legend_html = ''
        combined_df = pd.DataFrame()
        stats_df = pd.DataFrame()
        metric_df = pd.DataFrame()
        categorized_results = None

        if request.method == 'POST':
            file = request.files.get('file')
            if file and allowed_file(file.filename):
                filename = sanitize_filename(file.filename)
                session['file_name'] = filename

                try:
                    file_stream = io.BytesIO(file.read())
                    text = read_file(file_stream, filename)

                except Exception as e:
                    print(f"File reading error: {str(e)}")
                    return f"File reading error: {str(e)}"
            else:
                session.pop('file_name', None)
                text = request.form.get('text', '')
            
            
            text = normalize_text(text)

                        
            start = time.time()


    ### Fluency ###
            doc = nlp(text)

            num_sentences = len(list(doc.sents))

            total_words = 0
            sentslist = []
            for sentence in doc.sents:
                num_tokens = sum(1 for token in sentence if token.pos_ not in ["PUNCT", "SYM", "SPACE", "X"])  # Following TASSC_20058_stable.py
                total_words += num_tokens
                sentslist.append(sentence.text) 

            tokens = [token.text.lower() for token in doc if not token.is_punct and not token.is_space]
            type_count = len(set(tokens))

            ttr = safe_division(type_count, total_words)
            mls = safe_division(total_words, num_sentences)

            fluencytable = pd.DataFrame({
                "Index": ["Total Number of Words", "Number of Types", "Number of Sentences"],
                "Value": [total_words, type_count, num_sentences]
            })


    ### Complexity ###
            total_t_units = 0
            t_units_list = []
            clausal_data = []
            num_clauses = 0

            for i in sentslist:
                t_units = extract_t_units(i)
                filtered_t_units = [t for t in t_units if t]
                filtered_t_units = merge_punctuation(filtered_t_units)
                t_units_list.append(filtered_t_units)
                total_t_units += len(filtered_t_units)

                doc = nlp(i)
                clause_verbs = extract_verbs(doc)
                    
                clausal_data.append({
                    "sentence": i,
                    "total_clauses": len(clause_verbs),
                    "clause_verbs": clause_verbs
                })

                matched_t_units = []
                for t_unit, clause_info in zip(t_units_list, clausal_data):
                    if len(t_unit) == clause_info['total_clauses']:
                        matched_t_units.append(t_unit)
                    elif clause_info['total_clauses'] == 0:
                        matched_t_units.append(t_unit)        
                    else:
                        doc = nlp(clause_info['sentence'])
                        clause_verbs = extract_verbs(doc)
                        extracted_clauses = []
                        clauses = extract_clauses_using_verbs(doc, clause_verbs, extracted_clauses)
                        clauses_refined = refine_clauses(clauses)
                        output_with_missing_part = add_missing_part(clause_info['sentence'], clauses_refined)
                        output_with_missing_part = refine_clauses(output_with_missing_part)

                        if len(output_with_missing_part) == clause_info['total_clauses']:
                            matched_t_units.append(output_with_missing_part)

                clauses_only = []
                for t_unit in matched_t_units:
                    clauses_only.append(t_unit)

                clauses_refined = process_all_sentences(clauses_only)

                for i in range(len(clauses_refined)):
                    for j in range(len(clauses_refined[i]) - 1):
                        doc = nlp(clauses_refined[i][j])
                        last_token = doc[-1]
                        
                        if last_token.text.lower() in ["and", "but"] and last_token.pos_ == "CCONJ":
                            clauses_refined[i][j] = ''.join([token.text_with_ws for token in doc[:-1]]).strip()
                            clauses_refined[i][j + 1] = f"{last_token.text} {clauses_refined[i][j + 1]}"

                        elif last_token.text.lower() == "as":
                            clauses_refined[i][j] = ''.join([token.text_with_ws for token in doc[:-1]]).strip()
                            if j + 1 < len(clauses_refined[i]):
                                clauses_refined[i][j + 1] = f"as {clauses_refined[i][j + 1]}"
                            elif i + 1 < len(clauses_refined):
                                clauses_refined[i + 1].insert(0, f"as {clauses_refined[i + 1][0]}")

                clauses_refined = [[clause.replace(' ,', ',').replace(' .', '.').replace(' ?', '?').replace(' !', '!') for clause in sublist] for sublist in clauses_refined]

                num_clauses = sum(len(clause) for clause in clauses_refined)

            joined_string = " ".join(sentslist)
            vd_features = calculate_vp_deps(joined_string)
            nominal_features = calculate_nominal_deps(joined_string)

            mlc = format(safe_division(total_words, num_clauses), ".2f")
            mlt = format(safe_division(total_words, total_t_units), ".2f")
            c_t = format(safe_division(num_clauses, total_t_units), ".2f")

            dc_t = format(safe_division(vd_features["finite_dep_clause"], total_t_units), ".2f")
            dc_c = format(safe_division(vd_features["finite_dep_clause"], num_clauses), ".2f")

            mvd = format(safe_division(vd_features["vp_deps"], vd_features["finite_clause"]), ".2f")
            mnd = format(safe_division(nominal_features["np_deps"], nominal_features["np"]), ".2f")

            complexitytable = pd.DataFrame({
                "Index": ["Type-Token Ratio (TTR)","Mean Length of Sentence (MLS)", "Number of T-units", "Number of Clauses", "Mean Length of T-Unit (MLT)", "Mean Length of Clause (MLC)",
                          "Clauses per T-unit (C/T)", "Dependent Clauses per T-unit (DC/T)", "Dependent Clauses per Clause (DC/C)",
                          "Mean Verbal Dependents", "Mean Nominal Dependents"],
                "Value": [f"{ttr:.2f}", f"{mls:.2f}", total_t_units, num_clauses, mlt, mlc, c_t, dc_t, dc_c, mvd, mnd]
            })

    ### 追加 ###

            results = process_text(text)
            categorized_sentences = categorize_sentence_results(results)
            categorized_results = categorize_sentence_results(results)
            combined_df = create_analysis_dataframe(categorized_sentences)

            highlighted_sentences = []
            for result in categorized_results:
                highlighted = create_html_highlight(result['sentence'], result, show_legend=False)
                highlighted_sentences.append(highlighted)

            legend_html = create_legend()
            
            grammar_data = combined_df.copy()
            grammar_data.index = grammar_data.index + 1
            grammar_data.to_csv("static/files/complexity.csv", sep=",", index=False)

    ### Accuracy ###
            data = pd.DataFrame(sentslist, columns=['Sentence'])
            corrected_data = correct_sentences(data)
            corrected_data['Error Counts'] = corrected_data['Error Counts'].astype(int)
            corrected_data.index = corrected_data.index + 1

            corrected_list = corrected_data['Corrected'].tolist()

            error_report, t_units_counts, error_free_t_unit = check_error_in_t_units(corrected_list, t_units_list)

            clause_verbs_list = [entry['clause_verbs'] for entry in clausal_data]

            result = check_errors_in_t_units_and_clauses(corrected_list, t_units_list, clauses_refined)

            error_free_t_unit = result['error_free_t_unit']
            error_free_clause = result['error_free_clause']

            corrected_data['T-unit counts'] = result['t_units_counts']
            corrected_data['Error-free T-units'] = result['error_free_t_unit']
            corrected_data['Clause counts'] = result['clauses_counts']
            corrected_data['Error-free clauses'] = result['error_free_clause']
            corrected_data['Extracted T-units'] = t_units_list
            corrected_data['Extracted clauses'] = clauses_refined
            corrected_data['Clause signaling verbs'] = clause_verbs_list

            csv_data = corrected_data.copy()
            csv_data['Highlighted Original'] = csv_data['Highlighted Original'].str.replace('<strong>', '**')
            csv_data['Highlighted Original'] = csv_data['Highlighted Original'].str.replace('</strong>', '**')
            csv_data['Highlighted Corrected'] = csv_data['Highlighted Corrected'].str.replace('<strong>', '**')
            csv_data['Highlighted Corrected'] = csv_data['Highlighted Corrected'].str.replace('</strong>', '**')

            csv_data.to_csv("static/files/corrected.csv", sep=",", index=False)

            output_data['Original'] = corrected_data['Highlighted Original']
            output_data['Corrected'] = corrected_data['Highlighted Corrected']
            output_data['Error Counts'] = corrected_data['Error Counts'].copy()

            total_clauses = corrected_data['Clause counts'].sum()
            errorfree_sent_count = (corrected_data['Error Counts'] == 0).sum()
            errorfree_t_unit_count = corrected_data['Error-free T-units'].sum()
            errorfree_clause_count = corrected_data['Error-free clauses'].sum()

            # (1) Total Errors
            total_errors = corrected_data['Error Counts'].sum()
            # (2) Errors per 100 Words
            errors_per_hundred_words = (total_errors / total_words) * 100
            formatted_errors = format(errors_per_hundred_words, ".2f")
            # (3) Errors per Total Words
            number_of_errors_per_words = format(safe_division(total_errors, total_words), ".2f")
            # (4) Errors per sentences (errors / num_sentences)
            errors_per_sentence = format(safe_division(total_errors, num_sentences), ".2f")
            # (5) Errors per T-unit
            number_of_errors_per_t_unit = format(safe_division(total_errors, total_t_units), ".2f")
            # (6) Errors per Clause
            number_of_errors_per_clause = format(safe_division(total_errors, total_clauses), ".2f")
            # (7) Error-Free Sentences
            error_free_sentence = errorfree_sent_count
            # (8) Error-free T-units
            error_free_t_unit = errorfree_t_unit_count
            # (9) Error-free Clauses
            error_free_clause = errorfree_clause_count


            accuracytytable = pd.DataFrame({
                "Index": [
                    "Number of Errors", 
                    "Errors per 100 Words", 
                    "Errors per Total Words", 
                    "Errors per Sentence",
                    "Errors per T-Unit", 
                    "Errors per Clause", 
                    "Error-Free Sentences",
                    "Error-Free T-Units", 
                    "Error-Free Clauses"
                ],
                "Value": [
                    total_errors, 
                    formatted_errors, 
                    number_of_errors_per_words, 
                    errors_per_sentence,
                    number_of_errors_per_t_unit, 
                    number_of_errors_per_clause, 
                    error_free_sentence, 
                    error_free_t_unit, 
                    error_free_clause
                ]
            })
                

    ### 追加 ###

            stats_df = get_detailed_statistics(corrected_list, results)

            categorized_results = categorize_sentence_results(results)

            analysis_results = calculate_overall_syntactic_maturity(combined_df, corrected_list, categorized_results)


            metric_df = pd.DataFrame({
                'Index': [
                    'Overall Syntactic Maturity Score',
                    'Grammar Usage Rate',
                    'Grammar Diversity',
                    'Distribution Uniformity',
                    'Error-Free Rate',
                    'Total Grammar Items'
                ],
                'Value': [
                    analysis_results['overall_syntactic_maturity'],
                    analysis_results['grammar_usage_rate'],
                    analysis_results['grammar_diversity'],
                    analysis_results['distribution_uniformity'],
                    analysis_results['error_free_rate'],
                    analysis_results['total_grammar_items']
                ]
            })

            metric_df['Value'] = metric_df.apply(
                lambda row: f"{int(row['Value'])}" if row['Index'] == 'Total Grammar Items'
                else f"{row['Value']:.2f}", 
                axis=1
            )
            metric_df.index = ['']*len(metric_df)


            e_time = time.time() - start
            e_time = f"{e_time:.2f}" 



        file_name = session.get('file_name', '')
        
        return render_template('main.html', table1=[fluencytable.to_html(index=False)], 
                               table2=[complexitytable.to_html(index=False)],
                               table3=[accuracytytable.to_html(index=False)], 
                               table4=[output_data.to_html(classes='data', header="true", index=True, escape=False)],
                               table6=[stats_df.to_html(classes='data', header="true", index=True, escape=False)],
                               table7=[metric_df.to_html(classes='data', header="true", index=True, escape=False)],
                    
                               texts=text, e_time=e_time, file_name=file_name,
                               highlighted_sentences=highlighted_sentences,
                               legend_html=legend_html)

    except Exception as e:
        return str(e), 500
    


@app.route('/downloader1')
def downloader():
    return send_file('./static/files/corrected.csv',
                     mimetype='text/csv',
                     download_name='AccuracyReport.csv',
                     as_attachment=True)

@app.route('/downloader2', methods=['POST', 'GET'])
def downloader2():
    return send_file('./static/files/complexity.csv',
                     mimetype='text/csv',
                     download_name='ComplexityReport.csv',
                     as_attachment=True)



if __name__ == "__main__":
    Timer(1, open_browser).start()  # 1秒遅延してブラウザを開く
    app.run(port=5000, threaded=False)
    #app.run(debug=True, threaded=True) # web版の場合
