"""Matplotlib renderer for the invasion graph and its condensation."""

from __future__ import annotations

from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib.patches as mpatches  # type: ignore
import matplotlib.pyplot as plt  # type: ignore
import networkx as nx  # type: ignore

from .analysis import AnalysisResult
from .layout import compute_layout, compute_condensation_layout


ROLE_COLOR: Dict[str, str] = {
    "isolated":           "#d62728",   # strong red — stands out
    "clause_a_candidate": "#1f77b4",   # blue
    "in_cycle":           "#ff7f0e",   # orange
    "impotent":           "#7f7f7f",   # muted grey
    "transient":          "#bcbd22",   # olive (neutral)
}

SCC_BG_PALETTE: List[str] = [
    "#a6cee3", "#b2df8a", "#fb9a99", "#fdbf6f",
    "#cab2d6", "#ffff99", "#1f78b4", "#33a02c",
    "#e31a1c", "#ff7f00", "#6a3d9a", "#b15928",
]


def _bbox_for_members(
    pos: Dict[int, Tuple[float, float]], members: List[int], pad: float
) -> Tuple[float, float, float, float]:
    xs = [pos[v][0] for v in members]
    ys = [pos[v][1] for v in members]
    return min(xs) - pad, min(ys) - pad, max(xs) + pad, max(ys) + pad


def render_invasion(
    G_strict: nx.DiGraph,
    G_weak: nx.DiGraph,
    analysis: AnalysisResult,
    out_dir: Path,
    seed: int = 20260514,
) -> str:
    """Render results/invasion/graph.svg (and graph.png). Returns the
    backend name used for the layout (for the assumptions file).
    """
    out_dir = Path(out_dir)
    bot_names = [G_strict.nodes[v]["name"] for v in sorted(G_strict.nodes)]
    pos, backend = compute_layout(
        G_strict, analysis.condensation, analysis.topological_order,
        bot_names, seed=seed,
    )

    fig, ax = plt.subplots(figsize=(13, 9))
    ax.set_axis_off()

    # 1) SCC background boxes for non-singleton SCCs
    pad = 0.35
    for s in analysis.sccs:
        if s.size <= 1:
            continue
        x0, y0, x1, y1 = _bbox_for_members(pos, s.members, pad)
        color = SCC_BG_PALETTE[s.scc_id % len(SCC_BG_PALETTE)]
        rect = mpatches.FancyBboxPatch(
            (x0, y0), x1 - x0, y1 - y0,
            boxstyle="round,pad=0.18,rounding_size=0.25",
            linewidth=1.2, edgecolor=color, facecolor=color, alpha=0.18,
            zorder=0,
        )
        ax.add_patch(rect)
        ax.text(
            (x0 + x1) / 2, y1 + 0.18, f"SCC {s.scc_id} (size {s.size})",
            fontsize=8, color="#444", ha="center", va="bottom", zorder=1,
        )

    # 4) Nodes, coloured by role -- drawn first so we know their size for
    #    edge clipping. Edges are then drawn on top with arrowheads that
    #    terminate at the node boundary (min_target_margin).
    node_colors = [ROLE_COLOR[analysis.roles[v]] for v in G_strict.nodes]
    node_size = 1600
    nodes_artist = nx.draw_networkx_nodes(
        G_strict, pos,
        node_color=node_colors,
        node_size=node_size,
        edgecolors="#111",
        linewidths=1.2,
        ax=ax,
    )
    nodes_artist.set_zorder(2)

    # 2) Tie edges (dashed, light) -- drawn on top of nodes so arrowheads
    #    remain visible even though the underlying line is muted.
    tie_edges = [
        (u, v) for u, v, d in G_weak.edges(data=True) if d["is_tie"]
    ]
    if tie_edges:
        tie_collection = nx.draw_networkx_edges(
            G_weak, pos, edgelist=tie_edges,
            style="dashed", edge_color="#666", alpha=0.7,
            arrows=True, arrowstyle="-|>", arrowsize=22,
            connectionstyle="arc3,rad=0.18",
            width=1.3, ax=ax,
            node_size=node_size, min_source_margin=4, min_target_margin=12,
        )
        for patch in tie_collection:
            patch.set_zorder(3)

    # 3) Strict edges (solid)
    strict_edges = list(G_strict.edges)
    if strict_edges:
        strict_collection = nx.draw_networkx_edges(
            G_strict, pos, edgelist=strict_edges,
            edge_color="#111",
            arrows=True, arrowstyle="-|>", arrowsize=26,
            connectionstyle="arc3,rad=0.18",
            width=1.8, ax=ax,
            node_size=node_size, min_source_margin=4, min_target_margin=12,
        )
        for patch in strict_collection:
            patch.set_zorder(4)
    label_artists = nx.draw_networkx_labels(
        G_strict, pos,
        labels={v: G_strict.nodes[v]["name"] for v in G_strict.nodes},
        font_size=9, font_color="#111",
        ax=ax,
    )
    for text in label_artists.values():
        text.set_zorder(5)

    # 5) Legend
    role_patches = [
        mpatches.Patch(color=ROLE_COLOR[r], label=r)
        for r in ["isolated", "clause_a_candidate", "in_cycle",
                  "impotent", "transient"]
    ]
    # Add line-style entries
    from matplotlib.lines import Line2D
    line_patches = [
        Line2D([0], [0], color="#222", lw=1.6,
               label="strict invasion  (A[i,j] > A[j,j])"),
        Line2D([0], [0], color="#888", lw=1.2, linestyle="dashed",
               label="tie  (A[i,j] == A[j,j], clause-(b) territory)"),
    ]
    leg = ax.legend(
        handles=role_patches + line_patches,
        loc="lower center", bbox_to_anchor=(0.5, -0.06),
        ncol=4, frameon=False, fontsize=9,
    )
    leg.set_title("Invasion graph G> with weak ties overlaid", prop={"size": 10})

    ax.set_title(
        "OSGT invasion graph — solid = strict, dashed = tie. "
        "SCCs grouped, layered left-to-right.",
        fontsize=11, pad=12,
    )
    ax.margins(0.20)
    plt.tight_layout()
    fig.savefig(out_dir / "graph.svg", bbox_inches="tight")
    fig.savefig(out_dir / "graph.png", bbox_inches="tight", dpi=170)
    plt.close(fig)
    return backend


def render_condensation(
    G_strict: nx.DiGraph,
    analysis: AnalysisResult,
    out_dir: Path,
    seed: int = 20260514,
) -> str:
    out_dir = Path(out_dir)
    cond = analysis.condensation
    pos, backend = compute_condensation_layout(cond, seed=seed)

    fig, ax = plt.subplots(figsize=(11, 7))
    ax.set_axis_off()

    labels = {
        sid: f"SCC {sid}\n" + "\n".join(
            sorted(G_strict.nodes[v]["name"] for v in cond.nodes[sid]["members"])
        )
        for sid in cond.nodes
    }
    sizes = [1900 + 500 * len(cond.nodes[sid]["members"]) for sid in cond.nodes]
    colors = [
        SCC_BG_PALETTE[sid % len(SCC_BG_PALETTE)] if len(cond.nodes[sid]["members"]) > 1
        else "#e8e8e8"
        for sid in cond.nodes
    ]

    nodes_artist = nx.draw_networkx_nodes(
        cond, pos,
        node_color=colors, node_size=sizes,
        edgecolors="#111", linewidths=1.2, ax=ax,
    )
    nodes_artist.set_zorder(2)
    edge_collection = nx.draw_networkx_edges(
        cond, pos,
        edge_color="#111",
        arrows=True, arrowstyle="-|>", arrowsize=26,
        connectionstyle="arc3,rad=0.1",
        width=1.7, ax=ax,
        node_size=sizes, min_source_margin=6, min_target_margin=14,
    )
    for patch in edge_collection:
        patch.set_zorder(3)
    label_artists = nx.draw_networkx_labels(
        cond, pos, labels=labels, font_size=8, font_color="#111", ax=ax,
    )
    for text in label_artists.values():
        text.set_zorder(4)

    ax.set_title(
        f"Condensation DAG of G>: "
        f"{cond.number_of_nodes()} SCCs, "
        f"{cond.number_of_edges()} edges, topological layout.",
        fontsize=11, pad=12,
    )
    ax.margins(0.20)
    plt.tight_layout()
    fig.savefig(out_dir / "condensation.svg", bbox_inches="tight")
    fig.savefig(out_dir / "condensation.png", bbox_inches="tight", dpi=170)
    plt.close(fig)
    return backend
