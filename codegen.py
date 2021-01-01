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
    pass


if __name__ == "__main__":
    stdin = sys.stdin.read()
    print(case_gen(ast.literal_eval(stdin.strip())), end="")

