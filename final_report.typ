#set page(margin: (x: 1in, y: 1in))
#set text(font: "New Computer Modern", size: 11pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.")

#align(center)[
  #text(size: 16pt, weight: "bold")[
    Verified Pathfinding for Grid-Based Game AI
  ]

  CS6110 Final Project\
  Edward Stanford and Griffin Walker
]

= Abstract
Game AI often feels unfair because perception and planning are implemented with different assumptions. An enemy may react to hidden information or attempt a route that later turns out to be impossible. This project studies a verified version of that problem in a two-dimensional grid world. The goal is simple: an agent should only pursue targets it can currently see, and any returned path should respect the movement constraints of the map. The implementation is written in Dafny and combines rectangle-based field-of-view with A-star search. The current result is a working verified prototype for perception-constrained planning, together with a clear description of which guarantees are already proved and which remain future work.

= Introduction
Believable game AI should operate under the same informational limits as the player. In practice, this often fails. A common pattern is to compute a target using complete world state and only afterward ask a planner to justify the choice. Even when the resulting behavior is functional, it can look dishonest: the agent appears to know about hidden goals, to see through walls, or to commit to routes that later need to be repaired.

This project asks whether one narrow but important slice of game AI can be made honest by construction. The setting is a grid world with blocking and non-blocking obstacles, a single agent, and a set of candidate goals. The intended behavior is to compute the cells visible from the agent, select the most valuable visible target, and then produce a path that respects traversability. Rather than treating these as loosely coupled heuristics, the project encodes them in Dafny, a language and verifier for functional correctness (Leino 2010). The visibility component is based on the rectangle field-of-view formulation of Debenham and Solis-Oba (2020), while the planning component uses A-star search (Hart, Nilsson, and Raphael 1968).

The ideal version of the project would make three contributions. First, it would provide a reusable verified specification of visibility-aware pathfinding for grid-based agents. Second, it would prove strong end-to-end guarantees connecting visible goal selection to feasible planning. Third, it would show that such a verified core can still support practical integration in systems such as Unity or exported C-sharp code. The current project does not achieve the full version of that vision, but it does establish a credible core: visibility, goal choice, and pathfinding are composed in executable Dafny code rather than described only at the level of informal claims.

= Status
The project currently delivers a verified prototype, not a finished library. The strongest completed pieces are rectangle extraction, rectangle-based field-of-view, and an A-star implementation that reconstructs a feasible path through traversable cells. These modules run end-to-end in the provided demo and verify successfully under Dafny.

The main missing piece is the strongest end-to-end contract. The public `FindPath` interface does not yet prove that the chosen destination is the maximum-value visible goal, nor that the path is optimal in the full A-star sense. The implementation also does not yet include performance work, experiments, or engine integration. The rest of this report should therefore be read as documenting a correct and functioning core rather than a finished artifact.

= Demo
The demo in `src/main.dfy` builds a `25 x 25` world with four cell types: `Empty`, `High`, `Low`, and `Goal`. `High` cells block both movement and visibility. `Low` cells block movement but not visibility. This separation is important because it lets the example exercise both pathfinding and line-of-sight behavior.

The agent begins at `(12, 12)`. Three goals are placed at `(4, 16)`, `(15, 4)`, and `(20, 20)`. The value function assigns positive value only to visible goal cells, scaled by inverse Manhattan distance, so the agent prefers the nearest visible goal.

```dafny
var visibility_blocking := (c: Cell) => c == High;
var traversable := (c: Cell) => c != High && c != Low;
var value_function := (agent_pos: Point, target_pos: Point, cell: Cell) =>
  (if cell == Goal then 1.0 else 0.0) /
  (ManhattanDistance(agent_pos, target_pos) + 1) as real;

var pf := new Pathfinder<Cell>(grid, visibility_blocking, traversable);
var path, visible := pf.FindPath(agent_position, value_function);
```

In the observed run, the agent chooses the goal at `(4, 16)`. That goal is visible and scores better than the farther visible goal at `(20, 20)`. The goal at `(15, 4)` is not selected because it is outside the current field of view. The printed output also shows the path bending around `Low` cells instead of cutting through them:

```text

Path to Best Visible Goal:
                . . . . . . . . . . . . . . . . .
                . . . . . . . . . . . . . . . . .
                  . . . . . . . . . . . . . . . .
                  . . . . . . . . . . . . . . . .
                  . . . . . . . G @ . . . . . . .
          H H H H H . . . . . . . @ . L . . . . .
          H . . . . . . . . . . . @ . L . . . . .
          H . . . . . . L L L L L @ . L . . . . .
. .       H . . . . . . @ @ @ @ @ @ . L . . . . .
. . . . . H . . . . . . @ . . . . . . L . . . . .
. . . . . . . . . . . . @ . . . . . . . . . . . .
    . . . . . . . . . . @ . . . . . . . . . . . .
                H . . . A . . . . . . . . . . . .
                H . . . . . . . . . . . . . . . .
                H . . . . . . . . . . . . . . . .
                H . . . . . . . . . . . . . . . .
                H . . . . . . . . . . . . . . . .
                . . . . . . . . . . . . . . . . .
                . . . . . . . . . . . . . . . . .
              H H H . . . . . . . . . . . . . . .
                  . . . . . . . . . . . G . . . .
                  . . . . . . . . . . . . . . . .
                  . . . . . . . . . . . . . . . .
                . . . . . . . . . . . . . . . . .
                . . . . . . . . . . . . . . . . .

```

This example demonstrates the two main intended guarantees of the prototype: the selected target is visible, and the returned path is feasible with respect to the traversability relation.

= Implementation
The implementation is organized into four Dafny modules. `src/utils.dfy` defines shared concepts such as points, rectangles, and feasible paths. `src/visibility.dfy` contains the geometric core. It groups blocking cells into rectangles and computes field of view using a doubled-coordinate representation so that rays from cell centers can be reasoned about with integer arithmetic.

The key proof idea in the visibility module is that the executable computation is tied directly to a logical visibility specification. The method `CalculateFOV` updates a boolean visibility grid while maintaining correspondence with a predicate that describes whether a destination cell should be visible after processing a sequence of blocking rectangles. The module also includes rectangle extension logic to avoid false visibility gaps when blocking rectangles share a boundary.

`src/a_star.dfy` implements 4-connected A-star search. The proof effort there focuses on feasibility rather than shortest-path optimality: if the method returns a non-empty path, then the path starts at the source, ends at the goal, moves only between adjacent cells, and stays within traversable terrain. Finally, `src/pathfind.dfy` exposes the user-facing `Pathfinder<T>` abstraction. Its constructor caches blocking rectangles, and `FindPath` performs the overall pipeline: compute visibility, select a visible goal using a value function, and run A-star to that goal.

= Future Work
The most important next step is to strengthen the end-to-end specification. Ideally, `FindPath` should prove not only feasibility, but also that the chosen destination is the highest-value visible goal and that the returned path is optimal for the search metric being used. After that, the project should branch in two directions: engineering work to export or integrate the verified core into a game environment, and algorithmic work to add faster visibility variants while preserving the same specification.

= Discussion
The main lesson from this project is that verification was most useful exactly where conventional debugging would have been weakest. The field-of-view algorithm is easy to describe informally, but subtle near shared boundaries and corner cases. Writing the code in Dafny forced those cases to be expressed precisely.

Another lesson is that "verified" is not a binary label. The current system has strong local guarantees and weaker end-to-end ones. That is still meaningful progress, but the honest summary is narrower than "fully verified non-cheating AI." It is better described as a verified core for visibility-aware target selection and feasible pathfinding.

If I came back to this project after a long break, the first files to reread would be `src/visibility.dfy` and `src/pathfind.dfy`. The first contains the hardest geometric ideas, especially the doubled-coordinate model and rectangle extension. The second shows where the public API should eventually expose stronger guarantees than it does now.

= References
Debenham and Solis-Oba (2020). Evan R. M. Debenham and Roberto Solis-Oba. "New Algorithms for Computing Field of Vision over 2D Grids." In _Computer Science & Information Technology (CSCP 2020)_, pp. 1-18, 2020.

Hart, Nilsson, and Raphael (1968). Peter E. Hart, Nils J. Nilsson, and Bertram Raphael. "A Formal Basis for the Heuristic Determination of Minimum Cost Paths." _IEEE Transactions on Systems Science and Cybernetics_, 4(2):100-107, 1968.

Leino (2010). K. Rustan M. Leino. "Dafny: An Automatic Program Verifier for Functional Correctness." In _Proceedings of LPAR-16_, 2010.
