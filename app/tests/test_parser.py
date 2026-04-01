from pd_runner.lean.parser import parse_actions_from_stdout


def test_parse_actions_from_stdout_tuple_line() -> None:
    stdout = "(C, D)\n"
    left, right = parse_actions_from_stdout(stdout)
    assert left == "C"
    assert right == "D"


def test_parse_actions_from_stdout_prefixed_tokens() -> None:
    stdout = "(PD.Action.C, PD.Action.D)\n"
    left, right = parse_actions_from_stdout(stdout)
    assert left == "C"
    assert right == "D"
