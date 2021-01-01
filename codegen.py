import itertools
import subprocess
import ast
import sys

def case_gen(args):
    branches, always = args
    situations = itertools.product([True, False], repeat=len(branches))
    results = []
    for situation in situations:
        literals = []
        actions = set(always)
        for i, e in enumerate(situation):
            literals.append(f" ({branches[i][0]})" if e else f"!({branches[i][0]})")
            for action in branches[i][1] if e else []:
                actions.add(action)
        results.append((literals, actions))
    lines = []
    for result in results:
        condition = " ┆& ".join(result[0])
        actions = f"{{{', '.join(result[1])}}}"
        lines.append(f"{condition} ┆: {actions};")
    inputs = "\n".join(lines)
    outputs = subprocess.run("column -t -s '┆' -o '┆' | tr -d '┆'", shell=True, input=inputs.encode("utf-8"), capture_output=True).stdout.decode("utf-8")
    # remove last linebreak from output
    return outputs[:-1]

def case_gen_compact(args):
    def build_tree(d):
        return None if d == 0 else {True: build_tree(d - 1), False: build_tree(d - 1)}
    def fill_tree(tree, choices):
        current_choices = choices[: :]
        if tree[True] == None and tree[False] == None:
            tree[True] = get_actions(current_choices + [True])
            tree[False] = get_actions(current_choices + [False])
        else:
            fill_tree(tree[True], choices + [True])
            fill_tree(tree[False], choices + [False])
    def consolidate_tree(tree):
        if type(tree) == type({}):
            tree[True] = consolidate_tree(tree[True])
            tree[False] = consolidate_tree(tree[False])
            if tree[True] == tree[False]:
                return tree[True]
            else:
                return {True: tree[True], False: tree[False]}
        else:
            return tree

    branches, always = args
    def get_actions(choices):
        actions = set(always)
        for i, choice in enumerate(choices):
            if choice: [actions.add(action) for action in branches[i][1]]
        return actions

    situations_tree = build_tree(len(branches))
    fill_tree(situations_tree, [])
    situations_tree = consolidate_tree(situations_tree)
    print(situations_tree)




if __name__ == "__main__":
    stdin = sys.stdin.read()
    print(case_gen(ast.literal_eval(stdin.strip())), end="")

