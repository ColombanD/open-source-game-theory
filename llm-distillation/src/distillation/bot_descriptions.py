"""Hardcoded Python-pseudocode descriptions of the library bots.

These are the opponent descriptions injected into the per-bot prompt. We use
readable Python pseudocode (not the actual Lean source) so the model reasons
about the strategy rather than the engine's syntax. ``simulate(p, q)`` runs bot
``p`` against bot ``q``; ``proof_search(k, opp, hyp)`` is the bounded proof
oracle (returns True iff ``hyp`` is provable about ``opp`` within ``k`` steps).

Keys must cover every bot in the payoff matrix (canonical CSV order).
"""

from __future__ import annotations

BOT_DESCRIPTIONS: dict[str, str] = {
    "CooperateBot": """\
def CooperateBot(opp):
    return C  # always cooperate, ignoring the opponent
""",
    "CupodBot": """\
# Cooperate Unless Proof Of Defection.
def CupodBot(k, opp):
    if proof_search(k, opp, "opp(CupodBot(k)) == D"):
        return D  # proof opponent defects against me -> defect
    else:
        return C  # otherwise cooperate
""",
    "DBot": """\
def DBot(opp):
    if simulate(opp, DefectBot) == C:
        return D  # exploit opponents naive enough to cooperate against DefectBot
    else:
        return C  # otherwise cooperate
""",
    "DefectBot": """\
def DefectBot(opp):
    return D  # always defect, ignoring the opponent
""",
    "DupocBot": """\
# Defect Unless Proof Of Cooperation.
def DupocBot(k, opp):
    if proof_search(k, opp, "opp(DupocBot(k)) == C"):
        return C  # proof opponent cooperates against me -> cooperate
    else:
        return D  # otherwise defect
""",
    "OBot": """\
def OBot(opp):
    # Cooperate only with opponents that pass both probes.
    if simulate(opp, CooperateBot) == C:
        if simulate(opp, DefectBot) == C:
            return C  # cooperated against both probes
        else:
            return D  # cooperated only against CooperateBot
    else:
        return D  # failed the first probe
""",
    "TitForTatBot": """\
def TitForTatBot(opp):
    if simulate(opp, CooperateBot) == C:
        return C  # opponent looks cooperative -> cooperate
    else:
        return D  # otherwise defect
""",
    "EBot": """\
def EBot(opp):
    if simulate(opp, DefectBot) == C:
        return D  # exploit naive cooperator
    elif simulate(opp, CooperateBot) == C:
        return C  # reward cooperator
    elif simulate(opp, MirrorBot) == C:
        return C  # reward mirror
    else:
        return D
""",
    "CupodTrollBot": """\
def CupodTrollBot(k, opp):
    # Defect iff the opponent is literally CupodBot (structural identity).
    if opp == CupodBot(k):
        return D
    else:
        return C
""",
}
