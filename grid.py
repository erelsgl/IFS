"""
Utils for plotting
"""

import numpy as np

def peak_to_cartesian(p):
    """Transforms a 3D simplex coordinate into 2D Cartesian coordinates."""
    p = np.array(p)
    x = p[1] + 0.5 * p[2]
    y = p[2] * np.sqrt(3) / 2.0
    return x, y

def generate_simplex_grid(resolution=100):
    """Generates a dense grid of valid outcome distributions q over the 3-simplex."""
    grid = []
    for i in range(resolution + 1):
        for j in range(resolution + 1 - i):
            k = resolution - i - j
            grid.append([i / resolution, j / resolution, k / resolution])
    return np.array(grid)
