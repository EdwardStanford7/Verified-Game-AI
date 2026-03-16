include "utils.dfy"

module AStar {
  import opened Utils

  // Return the 4-directional traversable neighbors of p that lie within the grid.
  method GetNeighbors<T>(grid: array2<T>, p: Point, traversable: T -> bool) returns (neighbors: seq<Point>)
    requires ValidPoint(p, grid)
    ensures forall n :: n in neighbors ==> ValidPoint(n, grid) && traversable(grid[n.x, n.y])
  {
    neighbors := [];
    var candidates := [
      Point(p.x - 1, p.y), // N
      Point(p.x, p.y + 1), // E
      Point(p.x + 1, p.y), // S
      Point(p.x, p.y - 1) // W
    ];
    for i := 0 to 4
      invariant forall n :: n in neighbors ==> ValidPoint(n, grid) && traversable(grid[n.x, n.y])
    {
      var c := candidates[i];
      if ValidPoint(c, grid) && traversable(grid[c.x, c.y]) {
        neighbors := neighbors + [c];
      }
    }
  }

  // Return the index of the entry in s with the smallest first component.
  method FindMin(s: seq<(int, Point)>) returns (idx: int)
    requires |s| > 0
    ensures 0 <= idx < |s|
    ensures forall i :: 0 <= i < |s| ==> s[idx].0 <= s[i].0
  {
    idx := 0;
    for i := 1 to |s|
      invariant 0 <= idx < i
      invariant forall j :: 0 <= j < i ==> s[idx].0 <= s[j].0
    {
      if s[i].0 < s[idx].0 {
        idx := i;
      }
    }
  }

  // Walk came_from backwards from `goal` to reconstruct the path.
  // A step-counter prevents non-termination if the map were ever cyclic.
  method ReconstructPath<T>(came_from: map<Point, Point>, goal: Point, grid: array2<T>)
    returns (path: seq<Point>)
    requires ValidPoint(goal, grid)
    requires forall p :: p in came_from ==> ValidPoint(p,           grid)
    requires forall p :: p in came_from ==> ValidPoint(came_from[p], grid)
    ensures  forall i :: 0 <= i < |path| ==> ValidPoint(path[i], grid)
  {
    path := [];
    var current := goal;
    var limit   := grid.Length0 * grid.Length1 + 1;
    var steps   := 0;

    while current in came_from && steps < limit
      invariant ValidPoint(current, grid)
      invariant forall i :: 0 <= i < |path| ==> ValidPoint(path[i], grid)
      decreases limit - steps
    {
      path    := [current] + path;
      current := came_from[current];
      steps   := steps + 1;
    }
    // Prepend the start node (the one with no came_from entry).
    path := [current] + path;
  }

  // A* on a 4-connected grid.
  // Returns the optimal path from agent_position to goal, or [] if unreachable.
  method A_Star<T>(grid: array2<T>, agent_position: Point, goal: Point, traversable: T -> bool) returns (path: seq<Point>)
    ensures forall i :: 0 <= i < |path| ==> ValidPoint(path[i], grid)
  {
    path := [];

    // Guard: both endpoints must be inside the grid and passable.
    if !ValidPoint(agent_position, grid) || !ValidPoint(goal, grid) {
      return;
    }
    if !traversable(grid[agent_position.x, agent_position.y]) {
      return;
    }
    if !traversable(grid[goal.x, goal.y]) {
      return;
    }

    // Trivial case: already at the goal.
    if agent_position == goal {
      path := [agent_position];
      return;
    }

    // ---------- A* state ----------
    // open_set: (f-score, point) pairs; no strict heap, we do a linear scan.
    var open_set  : seq<(int, Point)> := [(ManhattanDistance(agent_position, goal), agent_position)];
    var came_from : map<Point, Point> := map[];
    var g_score   : map<Point, int>   := map[agent_position := 0];
    // visited plays the role of the closed set; avoids reasoning about |set|.
    var visited   := new bool[grid.Length0, grid.Length1]((i, j) => false);

    // Iteration budget: each productive step marks one cell visited,
    // so grid.Length0 * grid.Length1 productive steps suffice.
    var limit := grid.Length0 * grid.Length1 + 1;
    var iter  := 0;

    while |open_set| > 0 && iter < limit
      invariant iter <= limit
      invariant forall k :: 0 <= k < |open_set| ==> ValidPoint(open_set[k].1, grid)
      invariant forall p :: p in came_from ==> ValidPoint(p,            grid)
      invariant forall p :: p in came_from ==> ValidPoint(came_from[p], grid)
      decreases limit - iter
    {
      iter := iter + 1;

      // Pop the node with the lowest f-score.
      var min_idx := FindMin(open_set);
      var current := open_set[min_idx].1;
      open_set    := open_set[..min_idx] + open_set[min_idx + 1..];

      // Lazy deletion: skip nodes already finalized.
      if visited[current.x, current.y] {
        // Nothing to do; the outer decreases still decreases because iter grew.
      } else {
        // Goal test.
        if current == goal {
          path := ReconstructPath(came_from, current, grid);
          return;
        }

        visited[current.x, current.y] := true;

        // Relax edges to each passable neighbor.
        var neighbors := GetNeighbors(grid, current, traversable);
        var current_g := if current in g_score
        then g_score[current]
        else grid.Length0 * grid.Length1 + 1;

        var ni := 0;
        while ni < |neighbors|
          invariant ni <= |neighbors|
          invariant forall k :: 0 <= k < |open_set| ==> ValidPoint(open_set[k].1, grid)
          invariant forall p :: p in came_from ==> ValidPoint(p,            grid)
          invariant forall p :: p in came_from ==> ValidPoint(came_from[p], grid)
        {
          var neighbor    := neighbors[ni];
          ni := ni + 1;

          if !visited[neighbor.x, neighbor.y] {
            var tentative_g  := current_g + 1;
            var neighbor_g   := if neighbor in g_score
            then g_score[neighbor]
            else grid.Length0 * grid.Length1 + 1;

            if tentative_g < neighbor_g {
              came_from := came_from[neighbor := current];
              g_score   := g_score  [neighbor := tentative_g];
              var f     := tentative_g + ManhattanDistance(neighbor, goal);
              open_set  := open_set + [(f, neighbor)];
            }
          }
        }
      }
    }

    // No path found.
    path := [];
  }
}