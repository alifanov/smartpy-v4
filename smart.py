import ast
import time
import pickle
import os
import re
from exprs import exprs as exprs_db
import itertools


def get_heads(l):
    heads = []
    for s in l:
        if s:
            heads.append(s[0])
        else:
            heads.append([])
    return heads


def get_tails(l):
    tails = []
    for s in l:
        if s:
            tails.append(s[1:])
        else:
            tails.append([])
    return tails


class ASTTranslator(object):
    node_map = {
        'ClassDef': 'class',
        'Module': 'module',
        'Assign': '=',
        'Name': 'var',
        'Num': 'num',
        'FunctionDef': 'func',
        'Return': 'return',
        'Add': '+',
    }

    def walk(self, node):
        result = []
        node_name = node.__class__.__name__
        if node_name in self.node_map:
            node_name = self.node_map[node_name]
        if node_name == 'module':
            result += [node_name, list([self.walk(s) for s in node.body])]
        elif node_name == 'class':
            result += [node_name, node.name, list([self.walk(s) for s in node.body])]
        elif node_name == 'func':
            result += [node_name, node.name, [self.walk(s) for s in node.body]]
        elif node_name == '=':
            result += [node_name, self.walk(node.targets), self.walk(node.value)]
        elif node_name == 'return':
            result += [node_name, self.walk(node.value)]
        elif node_name == 'var':
            result = node.id
        elif node_name == 'BinOp':
            node_name = node.op.__class__.__name__
            node_name = self.node_map[node_name]
            result = [node_name, self.walk(node.left), self.walk(node.right)]
        elif node_name == 'Call':
            if node.func.attr == 'format':
                result = ['format', node.func.value.s,
                          [self.walk(s) for s in node.args]]  # TODO: add keywords, startargs, kwargs
        elif node_name == 'num':
            result = node.n
        elif node_name == 'list':
            if len(node) == 1:
                result = self.walk(node[0])
            else:
                result = list([self.walk(s) for s in node])
        else:
            result += [node_name, ]
        return result


def comparable(v):
    for cls in [
        str,
        int
    ]:
        if isinstance(v, cls): return True
    return False


class ASTPatternMatcher(object):
    def replace_all_list(self, l):
        if all([not isinstance(ll, list) for ll in l]):
            if all([ll == '*' for ll in l]):
                return '*'
            return l
        else:
            return [self.replace_all_list(ll) for ll in l]

    def replace_star_pairs(self, l):
        shift = 1
        res = l[:1]

        for i in range(len(l)):
            if l[i] == '*' and l[i + 1]:
                shift += 1
            if i + shift < len(l):
                if isinstance(l[i + shift], list):
                    res.append(self.replace_star_pairs(l[i + shift]))
                else:
                    res.append(l[i + shift])

        return res

    def make_simple_expr(self, e):
        e = self.replace_all_list(e)
        e = self.replace_star_pairs(e)
        return e

    def partial_compare_lists(self, l1, l2):
        if not isinstance(l1, list) and not isinstance(l2, list):
            return True

        if isinstance(l1, list) != isinstance(l2, list):
            return False

        if len(l1) != len(l2):
            return False

        result = []
        for e1, e2 in zip(l1, l2):
            if isinstance(e1, list) != isinstance(e2, list):
                return False
            else:
                result.append(self.partial_compare_lists(e1, e2))
        return True if result == [] else all(result)

    def check_in_list(self, el, l):
        for ll in l:
            if self.partial_compare_lists(el, ll):
                return True
        return False

    def get_common_expr(self, ast_list):
        # print('Expr[0]: {}'.format(ast_list[0]))
        # print('Expr[1]: {}'.format(ast_list[1]))
        # time.sleep(1)
        result = []

        heads = get_heads(ast_list)
        # print('Heads: {}'.format(heads))

        tails = get_tails(ast_list)
        # print('Tails: {}'.format(tails))

        if all([h == [] for h in heads]): return ''
        if any([h == [] for h in heads]): result.append('*')

        if all([comparable(el) for el in heads]):
            if len(set(heads)) == 1:  # compare
                result.append(heads[0])  # return common item
            else:
                result.append('?')  # differ
        else:
            if all([isinstance(h, list) for h in heads]):
                result += [self.get_common_expr(heads)]
        # print('Result: {}'.format(result))
        if tails[0]:
            if tails[0][0] and self.check_in_list(tails[0][0], tails[1]) and isinstance(tails[0][0], list) and len(
                    tails[0]) != len(
                    tails[1]):
                tails[0].insert(0, [])
        # print('Tails: {}'.format(tails))
        result += self.get_common_expr(tails)
        return result


class ASTGenerator(object):
    def __init__(self, code):
        self.code = code
        self.ast = ast.parse(code)
        self.parsed_ast = ASTTranslator().walk(self.ast)[1]


class CodeSearcher(object):
    def __init__(self, db):
        self.db = db

    def match_expr(self, query):
        expr, pattern = query

        heads = get_heads([expr, pattern])
        tails = get_tails([expr, pattern])

        if all([h == [] for h in heads]): return True

        if heads[1] == '*': return True

        if all([comparable(el) for el in heads]):
            if heads[1] == '*':
                return True
            if heads[1] == '?':
                if not heads[0]:
                    return False
                return True
            if heads[1] != heads[0]:
                return False
        else:
            if not self.match_expr(heads):
                return False
        return self.match_expr(tails)

    def search(self, expr):
        for k, v in self.db:
            if self.match_expr([expr, k]):
                return v
        return []


#TODO: move to ExprDB
class ExprSearcher(object):
    def __init__(self, db):
        self.db = db

    def extract_tags(self, s):
        m = re.findall(r'#([a-zA-Z^:space:]+)', s)
        return m

    def extract_cprops(self, s):
        m = re.findall(r'cprop ([a-z0-9]+)', s)
        return m

    def search(self, q, fuzzy=False):
        result = []
        tags = self.extract_tags(q)
        cprops = self.extract_cprops(q)
        for s, ex in self.db:
            if tags:
                db_tags = self.extract_tags(s)
                if set(db_tags) & set(tags):
                    result.append(ex)
                continue

            db_cprops = self.extract_cprops(s)
            if set(db_cprops) & set(cprops) or fuzzy:
                result.append(ex)
                continue
        return result


class ExprDB(object):
    db_name = 'exprs.pkl'
    db = []
    matcher = None

    def read_db(self):
        data = open(self.db_name, 'rb').read()
        if data:
            self.db = pickle.loads(data)
        else:
            return []

    def keys(self):
        return [rec[0] for rec in self.db]

    def save(self):
        f = open(self.db_name, 'wb')
        f.write(pickle.dumps(self.db))
        f.close()

    def __init__(self):
        self.read_db()
        self.matcher = ASTPatternMatcher()

    def update(self, rec, e, code):
        codes = rec[1] + [code,]
        codes = list(set(codes))
        new_rec = (e, codes)
        self.db = [new_rec if r == rec else rec for r in self.db]
        self.save()

    def flatten(self, l):
        res = []
        for ll in l:
            if isinstance(ll, list):
                res.extend(self.flatten(ll))
            else:
                res.append(ll)
        return res

    def add(self, e, code):
        if not self.db and self.db is not None:
            self.db.append(
                (e, [code,])
            )
        else:
            q = self.query(e, fuzzy=True)
            if q:
                self.update(q[0], q[0][0], code)
            else:
                for rec in self.db:
                    matched = self.matcher.get_common_expr([rec[0], e])
                    _matched = self.flatten(matched)
                    if not all([m == '*' for m in _matched]):
                        if matched == e:
                            self.update(rec, e, code)
                        else:
                            self.update(rec, matched, code)
                    else:
                        self.db.append(
                            (e, [code,])
                        )
        self.save()

    def query(self, q, fuzzy=False):
        res = []
        for rec in self.db:
            if fuzzy:
                if self.matcher.get_common_expr([q, rec[0]]) in [q, rec[0]]:
                    res.append(rec)
            else:
                if rec == q:
                    res.append(rec)
        return res


if __name__ == "__main__":
    BASE_DIR = 'codes/learn/'
    edb = ExprDB()
    exprs = []
    codes = []
    for f in os.listdir(BASE_DIR):
        path = os.path.join(BASE_DIR, f)
        if os.path.isfile(path):
            code = open(path).read()
            ast_expr = ASTGenerator(code).parsed_ast
            # print('AST: ', ast_expr)
            for ae in ast_expr:
                edb.add(ae, code)
                exprs.append(ae)
            # exprs.append(ast_expr)
            # codes.append(code)

    search_code = open(os.path.join('codes/search', 'source1.py')).read()

    ast_pm = ASTPatternMatcher()
    common_expr = ast_pm.get_common_expr(exprs)
    common_expr = ast_pm.make_simple_expr(common_expr)
    print(common_expr)

    # print('DB: {}'.format(edb.db))
    print(edb.query(['func', 'foo', [['return', ['+', 'bar', '?']]]], fuzzy=True))

    # TODO: add CodeItem class

    # code_db = [(common_expr, codes)]
    # s = CodeSearcher(code_db)
    #
    # expr = ASTGenerator(search_code).parsed_ast[0]
    # for code in s.search(expr):
    #     print('By code', code)
    #
    # es = ExprSearcher(exprs_db)
    # for expr in es.search('#base cprop v1', fuzzy=True):
    #     print('By expr: ', expr)
