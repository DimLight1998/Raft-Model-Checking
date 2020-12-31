import itertools
import subprocess
import ast
import sys

def case_gen(args):
    branches, fallback = args
    situations = itertools.product([True, False], repeat=len(branches))
    results = []
    for situation in situations:
        literals = []
        actions = set()
        for i, e in enumerate(situation):
            literals.append(f" ({branches[i][0]})" if e else f"!({branches[i][0]})")
            for action in [] if e else branches[i][1]:
                actions.add(action)
        if len(actions) == 0:
            actions = set(fallback)
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

if __name__ == "__main__":
    stdin = sys.stdin.read()
    print(case_gen(ast.literal_eval(stdin.strip())), end="")
    # print(case_gen([
    #     ("node0.role = Candidate", ["VoteReq", "Timeout"]),
    #     ("node1.role = Candidate", ["VoteReq", "Timeout"]),
    #     ("node2.role = Candidate", ["VoteReq", "Timeout"]),
    #     ("node0.role = Follower & node0.votedFor != -1", ["VoteRsp", "Timeout"]),
    #     ("node1.role = Follower & node1.votedFor != -1", ["VoteRsp", "Timeout"]),
    #     ("node2.role = Follower & node2.votedFor != -1", ["VoteRsp", "Timeout"]),
    # ], ["Noop", "Timeout"]))

