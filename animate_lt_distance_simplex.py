import os
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.tri as tri
from matplotlib.animation import FuncAnimation
from matplotlib.lines import Line2D

# Import shared layout helpers from grid.py
from grid import peak_to_cartesian, generate_simplex_grid

def animate_distance_contour(filename="lt_distance_evolution.gif", resolution=200, fps=5):
    """
    Animates a contour line through all points P in the simplex where 
    distance_t(A, P) == distance_t(A, B), with p ranging from 1 to 20.
    """
    # Ensure the output directory exists
    os.makedirs("plots", exist_ok=True)
    
    # 1. Define points A and B
    A = np.array([0.2, 0.3, 0.5])
    B = np.array([0.5, 0.2, 0.3])
    
    # 2. Project points A and B into 2D Cartesian coordinates for the plot background
    xA, yA = peak_to_cartesian(A)
    xB, yB = peak_to_cartesian(B)
    
    # 3. Generate high-resolution simplex grid for smooth contours
    q_points = generate_simplex_grid(resolution)
    xy_grid = np.array([peak_to_cartesian(q) for q in q_points])
    x, y = xy_grid[:, 0], xy_grid[:, 1]
    
    triangulation = tri.Triangulation(x, y)
    fig, ax = plt.subplots(figsize=(7, 6))
    
    # Define smoothly transitioning p-values from 1 up to 20
    # Combining linear space up to 5 and slightly larger steps up to 20
    p_values = np.concatenate([
        np.linspace(1.0, 5.0, num=17),
        np.linspace(6.0, 20.0, num=15)
    ])

    def update(frame_idx):
        p = p_values[frame_idx]
        ax.clear()
        
        # Draw static simplex triangle framework
        ax.plot([0, 1, 0.5, 0], [0, 0, np.sqrt(3)/2, 0], 'k-', lw=1.5)
        
        # Plot points A and B
        ax.scatter([xA], [yA], color='blue', s=130, marker='o', zorder=5, label=f'Point A {A}')
        ax.scatter([xB], [yB], color='darkorange', s=130, marker='s', zorder=5, label=f'Point B {B}')
        
        # Static Vertex Labels
        ax.text(-0.05, -0.05, 'Alt 1\n(1, 0, 0)', fontsize=10, ha='center', va='top')
        ax.text(1.05, -0.05, 'Alt 2\n(0, 1, 0)', fontsize=10, ha='center', va='top')
        ax.text(0.5, np.sqrt(3)/2 + 0.03, 'Alt 3\n(0, 0, 1)', fontsize=10, ha='center', va='bottom')
        
        # Calculate target distance threshold ||A - B||_t
        target_dist = (np.sum(np.abs(A - B) ** p)) ** (1.0 / p)
        
        # Calculate distance ||A - P||_t for every point P in our simplex grid
        grid_distances = np.zeros(len(q_points))
        for idx, P in enumerate(q_points):
            grid_distances[idx] = (np.sum(np.abs(A - P) ** p)) ** (1.0 / p)
            
        # Draw the contour line where distance equals the target
        ax.tricontour(triangulation, grid_distances, levels=[target_dist], 
                     colors=['red'], linestyles='--', linewidths=2.5, zorder=4)
        
        # Figure properties adjustments
        ax.set_xlim(-0.1, 1.1)
        ax.set_ylim(-0.1, 1.0)
        ax.axis('off')
        
        ax.set_title(f"Points $P$ where $\ell_t(A, P) = \ell_t(A, B)$\nSimplex Metrics | Current $p$ = {p:.2f}", 
                     fontsize=11, fontweight='bold')
        
        # Custom Legend handles
        contour_line = Line2D([0], [0], color='red', linestyle='--', lw=2.5, label='Equidistant Line')
        ax.legend(loc='upper right', fontsize=9)
        
        return ax.collections

    # Create and compile animation
    anim = FuncAnimation(fig, update, frames=len(p_values), interval=250, blit=False)
    output_path = os.path.join("plots", filename)
    
    print(f"Compiling equidistant line animation into {output_path}... Please wait.")
    anim.save(output_path, writer='pillow', fps=4)
    print(f"Animation successfully written to {output_path}")
    plt.close(fig)

if __name__ == "__main__":
    # Run the visualization sequence
    animate_distance_contour(filename="lt_distance_evolution.gif")