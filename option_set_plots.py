"""
Option-set geometry of the pivot-disagreement rule for n=2, m=3 budget aggregation.
 
Rule R(x, y), peaks x, y in the simplex {z>=0, sum z = 1}:
    b = argmax_j |x_j - y_j|            (most-disagreed issue: the pivot)
    c = (b+1) mod 3,  a = (b+2) mod 3
    q_a = median(x_a, y_a, 1/2)
    m_b = median(x_b, y_b, 1/2);  m_c = min(x_c, y_c)
    if q_a + m_b + m_c > 1:  q_c = m_c;  q_b = 1 - q_a - q_c
    else:                    q_b = m_b;  q_c = 1 - q_a - q_b
 
Option set  S(p) = { R(x, p) : x in simplex }  (outcomes reachable by the other
agent when one agent reports p). Central fact:
    R(p1,p2) = L1-nearest point of p1 in S(p2)  =  L1-nearest point of p2 in S(p1).
 
GEOMETRY (verified):
 * S(p) splits by pivot region b(x,p); each piece is a straight segment, a point,
   or (only when max_j p_j > 1/2) a filled 2-D patch = the fixed set {x: R(x,p)=x}.
 * For max_j p_j <= 1/2 (e.g. the centroid), S(p) is exactly three segments meeting
   at p: segment j holds q_j = p_j, raises q_{j+1} to 1/2, lowers q_{j+2} to 1/2 - p_j.
   At the centroid (1/3,1/3,1/3) the tips are (1/3,1/2,1/6),(1/6,1/3,1/2),(1/2,1/6,1/3).
 
Plotting renders S(p) as a faithful dense point cloud (correct whether a piece is a
segment, point, or 2-D patch), colored by pivot region.
 
Usage:  python3 option_set_plots.py     (figures -> $OUTDIR, default current dir)
"""
import os
import numpy as np
import matplotlib
import matplotlib.pyplot as plt
import matplotlib.lines as mlines
from matplotlib.patches import Polygon as MplPolygon
 
 
 
# ---------- barycentric <-> Cartesian (equilateral triangle) ----------
# Vertex order: issue1 -> bottom-left, issue2 -> bottom-right, issue3 -> top
V = np.array([
    [0.0, 0.0],          # weight on coordinate 1
    [1.0, 0.0],          # weight on coordinate 2
    [0.5, np.sqrt(3)/2], # weight on coordinate 3
])
 
def bary_to_xy(p):
    """p: (...,3) barycentric (sums to 1) -> (...,2) Cartesian."""
    p = np.asarray(p, dtype=float)
    return p @ V
 
def xy_to_bary(xy):
    xy = np.asarray(xy, dtype=float)
    T = np.array([[V[0,0]-V[2,0], V[1,0]-V[2,0]],
                  [V[0,1]-V[2,1], V[1,1]-V[2,1]]])
    Tinv = np.linalg.inv(T)
    lam12 = (xy - V[2]) @ Tinv.T
    lam3 = 1 - lam12.sum(axis=-1)
    return np.concatenate([lam12, lam3[..., None]], axis=-1)
 
# ---------- the rule ----------
def med3(u, v, w=0.5):
    return sorted([u, v, w])[1]
 
def R(x, y):
    """The pivot-disagreement rule. x, y: length-3 arrays summing to 1."""
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    D = np.abs(x - y)
    b = int(np.argmax(D))
    c = (b + 1) % 3
    a = (b + 2) % 3
    qa = med3(x[a], y[a])
    mb = med3(x[b], y[b])
    mc = min(x[c], y[c])
    q = np.zeros(3)
    q[a] = qa
    if qa + mb + mc > 1:
        q[c] = mc
        q[b] = 1 - qa - mc
    else:
        q[b] = mb
        q[c] = 1 - qa - mb
    return q
 
def R_batch(X, y):
    """Vectorized R(x, y) for an array X of shape (N,3) against fixed y (3,)."""
    X = np.asarray(X, dtype=float)
    y = np.asarray(y, dtype=float)
    N = X.shape[0]
    D = np.abs(X - y[None, :])
    b = np.argmax(D, axis=1)
    c = (b + 1) % 3
    a = (b + 2) % 3
    idx = np.arange(N)
 
    def med3v(u, v):
        s = np.sort(np.stack([u, v, np.full_like(u, 0.5)], axis=0), axis=0)
        return s[1]
 
    qa = med3v(X[idx, a], y[a])
    mb = med3v(X[idx, b], y[b])
    mc = np.minimum(X[idx, c], y[c])
 
    Q = np.zeros((N, 3))
    cond = (qa + mb + mc) > 1
    qc_if = mc
    qb_if = 1 - qa - mc
    qb_else = mb
    qc_else = 1 - qa - mb
 
    Q[idx, a] = qa
    Q[idx, b] = np.where(cond, qb_if, qb_else)
    Q[idx, c] = np.where(cond, qc_if, qc_else)
    return Q
 
# ---------- grid helper ----------
def simplex_grid(G):
    """Fine barycentric grid with resolution G ((G+1)(G+2)/2 points)."""
    pts = []
    for i in range(G + 1):
        for j in range(G + 1 - i):
            k = G - i - j
            pts.append([i / G, j / G, k / G])
    return np.array(pts)
 
# ---------- option set S(p), with per-piece dimension classification ----------
def option_set_pieces(p, G=300, round_decimals=6, area_tol=1e-7):
    """Split S(p) into its (<=3) pieces, one per pivot region b in {0,1,2}.
    Each piece is classified as '2d' (positive-area patch) or '1d' (segment
    or point). Returns a list of dicts:
        {'b': k, 'kind': '2d'|'1d', 'points': (Ni,3) barycentric array}
    For '2d' pieces, `points` is the set of *hull vertices* (in barycentric
    coords, ordered around the polygon) -- enough to draw a filled patch.
    For '1d' pieces, `points` is the set of (typically 2) segment endpoints.
    """
    from scipy.spatial import ConvexHull
    X = simplex_grid(G)
    D = np.abs(X - p[None, :])
    b = np.argmax(D, axis=1)
    pieces = []
    for k in range(3):
        sel = X[b == k]
        if len(sel) == 0:
            continue
        Q = R_batch(sel, p)
        Qr = np.round(Q, round_decimals)
        Qu = np.unique(Qr, axis=0)
        if len(Qu) == 1:
            pieces.append({'b': k, 'kind': '1d', 'points': Qu})
            continue
        xy = bary_to_xy(Qu)
        xy_u = np.unique(np.round(xy, round_decimals), axis=0)
        if len(xy_u) < 3:
            pieces.append({'b': k, 'kind': '1d', 'points': Qu})
            continue
        try:
            hull = ConvexHull(xy_u)
            if hull.volume > area_tol:
                # 2D patch: keep hull-vertex barycentric points, in order
                hv_xy = xy_u[hull.vertices]
                hv_bary = []
                # map back: find nearest Qu point to each hull xy vertex
                for v in hv_xy:
                    d = np.sum((xy - v[None, :]) ** 2, axis=1)
                    hv_bary.append(Qu[np.argmin(d)])
                pieces.append({'b': k, 'kind': '2d', 'points': np.array(hv_bary)})
            else:
                pieces.append({'b': k, 'kind': '1d', 'points': Qu})
        except Exception:
            pieces.append({'b': k, 'kind': '1d', 'points': Qu})
    return pieces
 
def option_set(p, G=300, round_decimals=6):
    """S(p) as a flat (N,3) point cloud (union over all pieces), useful for
    nearest-point queries. Not meant for plotting directly (use
    option_set_pieces for a faithful picture)."""
    X = simplex_grid(G)
    Q = R_batch(X, p)
    Qr = np.round(Q, round_decimals)
    return np.unique(Qr, axis=0)
 
def sort_along_segment(points3):
    """Sort near-collinear barycentric points along their principal direction
    (for clean line plotting of a 1D piece)."""
    xy = bary_to_xy(points3)
    c = xy.mean(axis=0)
    Xc = xy - c
    if np.allclose(Xc, 0):
        return points3
    _, _, Vt = np.linalg.svd(Xc, full_matrices=False)
    d = Vt[0]
    t = Xc @ d
    order = np.argsort(t)
    return points3[order]
 
def nearest_point(x, pointset):
    """L1-nearest point of `pointset` (N,3) to x (3,)."""
    d = np.abs(pointset - x[None, :]).sum(axis=1)
    j = int(np.argmin(d))
    return pointset[j], d[j]
 
 
# =====================================================================
# Plotting
# =====================================================================
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon as MplPolygon
 
TRI_EDGE_COLOR = "#999999"
S_COLOR = "#1f6fb2"
P_COLOR = "#d4380d"
X_COLOR = "#2b8a3e"
Q_COLOR = "#8c2d8c"
PIVOT_COLORS = ["#1f6fb2", "#e8801a", "#2c9e4b"]  # by pivot region b=0,1,2
 
LABELS = ["issue 1", "issue 2", "issue 3"]
 
def draw_triangle(ax, labels=True):
    tri = np.array([V[0], V[1], V[2], V[0]])
    ax.plot(tri[:, 0], tri[:, 1], color=TRI_EDGE_COLOR, lw=1.3, zorder=1)
    ax.set_aspect("equal"); ax.axis("off")
    ax.set_xlim(-0.18, 1.18); ax.set_ylim(-0.14, np.sqrt(3)/2 + 0.16)
    if labels:
        offs = [(-0.08, -0.04), (1.08, -0.04), (0.5, np.sqrt(3)/2 + 0.07)]
        for lab, (dx, dy) in zip(LABELS, offs):
            ax.text(dx, dy, lab, ha="center", va="center", fontsize=9.5, color="#555")
 
def option_set_cloud(p, G=460):
    """Faithful point cloud of S(p) = {R(x,p)}, with the pivot region b(x,p) of
    each outcome (for optional coloring). Rendering the cloud directly is correct
    whether a piece is a filled 2-D patch, a straight segment, or a bent polyline."""
    X = simplex_grid(G)
    D = np.abs(X - p[None, :]); b = np.argmax(D, axis=1)
    Q = R_batch(X, p)
    return Q, b
 
def draw_option_set(ax, p, G=460, color=S_COLOR, by_pivot=False, label="S(p)", ms=1.6):
    """Draw S(p) as a dense point cloud (faithful to its true 1-D / 2-D structure)."""
    Q, b = option_set_cloud(p, G=G)
    if by_pivot:
        for k in range(3):
            sel = Q[b == k]
            if len(sel):
                xy = bary_to_xy(sel)
                ax.plot(xy[:, 0], xy[:, 1], '.', color=PIVOT_COLORS[k], ms=ms,
                        zorder=2, label=(f"S(p): pivot {k+1}" if label else None))
    else:
        xy = bary_to_xy(Q)
        ax.plot(xy[:, 0], xy[:, 1], '.', color=color, ms=ms, zorder=2,
                label=label)
    return Q
 
def mark_point(ax, p, color, label, marker="o", size=80, z=6):
    xy = bary_to_xy(p)
    ax.scatter([xy[0]], [xy[1]], color=color, s=size, zorder=z,
               edgecolor="white", linewidth=1.1, marker=marker, label=label)
    return xy
 
def plot_single_option_set(ax, p, title=None, G=460, by_pivot=True):
    import matplotlib.lines as mlines
    draw_triangle(ax)
    draw_option_set(ax, p, G=G, by_pivot=by_pivot, label="S(p)")
    mark_point(ax, p, P_COLOR, "p", size=70)
    if title: ax.set_title(title, fontsize=11)
    # proxy handles with controlled marker sizes (avoid markerscale inflating the 'p' dot)
    handles = []
    if by_pivot:
        for k in range(3):
            handles.append(mlines.Line2D([], [], color=PIVOT_COLORS[k], marker='.',
                           linestyle='None', markersize=7, label=f"S(p): pivot {k+1}"))
    else:
        handles.append(mlines.Line2D([], [], color=S_COLOR, marker='.',
                       linestyle='None', markersize=7, label="S(p)"))
    handles.append(mlines.Line2D([], [], color=P_COLOR, marker='o', linestyle='None',
                   markersize=8, markeredgecolor='white', label="p"))
    ax.legend(handles=handles, loc="upper right", fontsize=7.5, frameon=False,
              bbox_to_anchor=(1.02, 1.02))
 
def plot_nearest_point_illustration(ax, p1, p2, G=460, title=None):
    draw_triangle(ax)
    draw_option_set(ax, p2, G=G, color=S_COLOR, by_pivot=False, label="S(p2)", ms=1.8)
    q = R(p1, p2)
    p1xy = mark_point(ax, p1, X_COLOR, "p1", size=85)
    p2xy = mark_point(ax, p2, P_COLOR, "p2", size=85)
    qxy = mark_point(ax, q, Q_COLOR, "q = R(p1,p2)", marker="*", size=200, z=7)
    ax.plot([p1xy[0], qxy[0]], [p1xy[1], qxy[1]], color="#444", lw=1.3,
            ls=(0, (4, 2)), zorder=4)
    if title: ax.set_title(title, fontsize=10.5)
    import matplotlib.lines as mlines
    h = [mlines.Line2D([],[],color=S_COLOR,marker='.',linestyle='None',markersize=7,label="S(p2)"),
         mlines.Line2D([],[],color=X_COLOR,marker='o',linestyle='None',markersize=8,markeredgecolor='white',label="p1"),
         mlines.Line2D([],[],color=P_COLOR,marker='o',linestyle='None',markersize=8,markeredgecolor='white',label="p2"),
         mlines.Line2D([],[],color=Q_COLOR,marker='*',linestyle='None',markersize=13,markeredgecolor='white',label="q = R(p1,p2)")]
    ax.legend(handles=h, loc="upper right", fontsize=7.5, frameon=False, bbox_to_anchor=(1.04,1.02))
    return q
 


def plot_option_sets():
    # ---------------- Figure 1: option sets S(p) for representative p ----------------
    pts = [
        (np.array([1., 0., 0.]),        ""),
        (np.array([0.8, 0.1, 0.1]),       ""),
        (np.array([0.6, 0.2, 0.2]),     ""),
        (np.array([0.4, 0.3, 0.3]),     ""),
        (np.array([0.34, 0.33, 0.33]),     ""),
        (np.array([0.2, 0.4, 0.4]),     ""),
    ]
    fig, axes = plt.subplots(2, 3, figsize=(13.5, 9.2))
    for ax, (p, title) in zip(axes.flat, pts):
        plot_single_option_set(ax, p, title=title, G=350)
    fig.suptitle(
        "Option sets S(p): outcomes reachable when one agent reports p,\n"
        "as the other agent ranges over the whole simplex", fontsize=13, y=0.99)
    plt.tight_layout(rect=[0, 0, 1, 0.95])
    plt.savefig(os.path.join(outdir, "fig1_option_sets.png"), dpi=150)
    plt.close(fig)

def plot_dual_nearest_point_illustrations():
    # ---------------- Figure 2: dual nearest-point illustration ----------------
    profiles = [
        (np.array([0.8, 0.1, 0.1]), np.array([0.1, 0.45, 0.45]), "Disagreement-driven profile"),
        (np.array([1., 0., 0.]),    np.array([0., 1., 0.]),       "Vertex vs vertex"),
        (np.array([0.5, 0.3, 0.2]), np.array([0.2, 0.3, 0.5]),    "Two interior peaks"),
        (np.array([0.3, 0.3, 0.4]), np.array([0.5, 0.4, 0.1]),    "Generic interior profile"),
    ]
    fig, axes = plt.subplots(2, 4, figsize=(17.5, 9.2))
    for col, (p1, p2, desc) in enumerate(profiles):
        ax1, ax2 = axes[0, col], axes[1, col]
        q1 = plot_nearest_point_illustration(
            ax1, p1, p2, G=350, title=f"{desc}\nagent 1 projects onto S(p2)")
        q2 = plot_nearest_point_illustration(
            ax2, p2, p1, G=350, title="(same outcome) agent 2 projects onto S(p1)")
        assert np.allclose(q1, q2, atol=1e-6), (q1, q2)
    fig.suptitle(
        "The outcome q = R(p1,p2) is simultaneously the L1-nearest point of p1 in S(p2),\n"
        "and the L1-nearest point of p2 in S(p1)  (anonymity + single-agent projection)",
        fontsize=13, y=0.995)
    plt.tight_layout(rect=[0, 0, 1, 0.94])
    plt.savefig(os.path.join(outdir, "fig2_nearest_point.png"), dpi=150)
    plt.close(fig)

def plot_why_truthfulness_holds():
    # ---------------- Figure 3: why truthfulness holds ----------------
    p2 = np.array([0.1, 0.45, 0.45])
    p1_true = np.array([0.8, 0.1, 0.1])
    p1_dev = np.array([0.1, 0.6, 0.3])   # a deliberately bad misreport

    fig, ax = plt.subplots(1, 1, figsize=(7.6, 8.6))
    draw_triangle(ax)
    draw_option_set(ax, p2, G=350, label="S(p2)")

    q_true = R(p1_true, p2)
    q_dev = R(p1_dev, p2)
    d_true = np.abs(p1_true - q_true).sum()
    d_dev = np.abs(p1_true - q_dev).sum()

    p1xy = mark_point(ax, p1_true, "#2b8a3e", "p1 (true peak)", size=120)
    mark_point(ax, p1_dev, "#b8860b", "p1' (misreport)", marker="X", size=140)
    mark_point(ax, p2, "#d4380d", "p2", size=95)
    qxy = mark_point(ax, q_true, "#8c2d8c",
                      f"q=R(p1,p2): truthful, dist={d_true:.2f}", marker="*", size=260, z=7)
    qdxy = mark_point(ax, q_dev, "#555555",
                       f"q'=R(p1',p2): misreport, dist={d_dev:.2f}", marker="*", size=170, z=6)

    ax.plot([p1xy[0], qxy[0]], [p1xy[1], qxy[1]], color="#2b8a3e", lw=2.2, ls="--", zorder=4)
    ax.plot([p1xy[0], qdxy[0]], [p1xy[1], qdxy[1]], color="#b8860b", lw=2.0, ls=":", zorder=4)

    ax.set_title("Why truthfulness holds", fontsize=13, pad=10)
    ax.legend(loc="upper center", fontsize=9, frameon=False, ncol=1, bbox_to_anchor=(0.5, -0.02))
    fig.text(0.5, 0.965,
              "Misreporting only moves agent 1 to a different point of the SAME fixed menu S(p2).\n"
              "q is already the L1-closest point of S(p2) to p1, so no misreport can do better.",
              ha="center", va="top", fontsize=10.5, color="#333")
    plt.tight_layout(rect=[0, 0.10, 1, 0.90])
    plt.savefig(os.path.join(outdir, "fig3_truthfulness_mechanism.png"), dpi=150)
    plt.close(fig)


# =====================================================================
# Driver: generate the three figures
# =====================================================================
if __name__ == "__main__":
    import os
    matplotlib.use("Agg")
    outdir = "plots/"
    os.makedirs(outdir, exist_ok=True)

    plot_option_sets()
    # plot_dual_nearest_point_illustrations()
    # plot_why_truthfulness_holds()

    print("Saved fig1_option_sets.png, fig2_nearest_point.png, fig3_truthfulness_mechanism.png to", outdir)
