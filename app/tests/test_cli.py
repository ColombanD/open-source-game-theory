import sys

import pytest

from pd_runner import cli
from pd_runner.models import MatchupResult


def test_cli_main_reports_proof_line(monkeypatch, capsys) -> None:
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "pd-runner",
            "--left",
            "cooperateBot",
            "--right",
            "defectBot",
        ],
    )
    monkeypatch.setattr(
        cli,
        "run_matchup",
        lambda request, keep_file=True: MatchupResult(
            left_bot=request.left_bot,
            right_bot=request.right_bot,
            left_action="C",
            right_action="D",
            lean_file="/tmp/matchup.lean",
            command="lake env lean /tmp/matchup.lean",
            proof_theorem_used="PD.Proofs.OpenSourceBots.cd_actionClaim",
        ),
    )

    cli.main()

    output = capsys.readouterr().out
    assert "proof:     PD.Proofs.OpenSourceBots.cd_actionClaim" in output
    assert "actions:   (C, D)" in output


def test_cli_main_quiet_mode_emits_only_action_tuple(monkeypatch, capsys) -> None:
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "pd-runner",
            "--left",
            "cooperateBot",
            "--right",
            "defectBot",
            "--quiet",
        ],
    )
    monkeypatch.setattr(
        cli,
        "run_matchup",
        lambda request, keep_file=True: MatchupResult(
            left_bot=request.left_bot,
            right_bot=request.right_bot,
            left_action="C",
            right_action="D",
            lean_file="/tmp/matchup.lean",
            command="lake env lean /tmp/matchup.lean",
            proof_theorem_used="PD.Proofs.OpenSourceBots.cd_actionClaim",
        ),
    )

    cli.main()

    output = capsys.readouterr().out.strip()
    assert output == "(C, D)"


def test_cli_main_json_mode_emits_json_payload(monkeypatch, capsys) -> None:
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "pd-runner",
            "--left",
            "cooperateBot",
            "--right",
            "defectBot",
            "--json",
        ],
    )
    monkeypatch.setattr(
        cli,
        "run_matchup",
        lambda request, keep_file=True: MatchupResult(
            left_bot=request.left_bot,
            right_bot=request.right_bot,
            left_action="C",
            right_action="D",
            lean_file="/tmp/matchup.lean",
            command="lake env lean /tmp/matchup.lean",
            proof_theorem_used="PD.Proofs.OpenSourceBots.cd_actionClaim",
        ),
    )

    cli.main()

    output = capsys.readouterr().out
    assert '"left_bot": "cooperateBot"' in output
    assert '"proof_theorem_used": "PD.Proofs.OpenSourceBots.cd_actionClaim"' in output


def test_cli_main_rejects_single_claim_side(monkeypatch, capsys) -> None:
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "pd-runner",
            "--left",
            "cooperateBot",
            "--right",
            "defectBot",
            "--claim-left",
            "C",
        ],
    )

    with pytest.raises(SystemExit):
        cli.main()

    stderr = capsys.readouterr().err
    assert "--claim-left and --claim-right must be provided together" in stderr