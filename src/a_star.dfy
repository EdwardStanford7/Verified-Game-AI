include "utils.dfy"

module AStar {
  import opened Utils

  // Return the 4-directional traversable neighbors of p that lie within the grid.
  method GetNeighbors<T>(grid: array2<T>, p: Point, traversable: T -> bool) returns (neighbors: seq<Point>)
    requires ValidPoint(p, grid)
    ensures forall n :: n in neighbors ==> WalkablePoint(n, grid, traversable)
    ensures forall n :: n in neighbors ==> Adjacent(p, n)
  {
    neighbors := [];

    var north := Point(p.x - 1, p.y);
    if ValidPoint(north, grid) && traversable(grid[north.x, north.y]) {
      neighbors := neighbors + [north];
    }

    var east := Point(p.x, p.y + 1);
    if ValidPoint(east, grid) && traversable(grid[east.x, east.y]) {
      neighbors := neighbors + [east];
    }

    var south := Point(p.x + 1, p.y);
    if ValidPoint(south, grid) && traversable(grid[south.x, south.y]) {
      neighbors := neighbors + [south];
    }

    var west := Point(p.x, p.y - 1);
    if ValidPoint(west, grid) && traversable(grid[west.x, west.y]) {
      neighbors := neighbors + [west];
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

  // Walk came_from backwards from goal to reconstruct a feasible path.
  method ReconstructPath<T>(
    came_from: map<Point, Point>,
    g_score: map<Point, int>,
    start: Point,
    goal: Point,
    grid: array2<T>,
    traversable: T -> bool)
    returns (path: seq<Point>)
    requires start in g_score && g_score[start] == 0
    requires goal in g_score
    requires forall p :: p in g_score ==> 0 <= g_score[p]
    requires forall p :: p in g_score ==> WalkablePoint(p, grid, traversable)
    requires forall p :: p in g_score && p != start ==> p in came_from
    requires forall p :: p in came_from ==> p in g_score && came_from[p] in g_score
    requires forall p :: p in came_from ==> Adjacent(came_from[p], p)
    requires forall p :: p in came_from ==> g_score[came_from[p]] + 1 == g_score[p]
    ensures FeasiblePath(path, start, goal, grid, traversable)
    ensures |path| == g_score[goal] + 1
  {
    path := [goal];
    var current := goal;

    while current != start
      invariant current in g_score
      invariant 0 <= g_score[current]
      invariant 0 < |path|
      invariant path[0] == current
      invariant path[|path| - 1] == goal
      invariant WalkablePath(path, grid, traversable)
      invariant ConsecutivePath(path)
      invariant |path| + g_score[current] == g_score[goal] + 1
      decreases g_score[current]
    {
      var child := current;
      var parent := came_from[child];
      var old_path := path;

      path := [parent] + old_path;
      current := parent;
    }
  }

  // A* on a 4-connected grid.
  // Returns a feasible path from agent_position to goal, or [] if no path is found.
  method A_Star<T>(grid: array2<T>, agent_position: Point, goal: Point, traversable: T -> bool) returns (path: seq<Point>)
    ensures path == [] || FeasiblePath(path, agent_position, goal, grid, traversable)
    ensures !ValidPoint(agent_position, grid) || !ValidPoint(goal, grid) ==> path == []
    ensures ValidPoint(agent_position, grid) && !traversable(grid[agent_position.x, agent_position.y]) ==> path == []
    ensures ValidPoint(goal, grid) && !traversable(grid[goal.x, goal.y]) ==> path == []
    ensures WalkablePoint(agent_position, grid, traversable) && agent_position == goal ==> path == [agent_position]
    ensures forall p :: p in path ==> WalkablePoint(p, grid, traversable)
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
      assert FeasiblePath(path, agent_position, goal, grid, traversable);
      return;
    }

    // ---------- A* state ----------
    // open_set: (f-score, point) pairs; no strict heap, we do a linear scan.
    var open_set  : seq<(int, Point)> := [(ManhattanDistance(agent_position, goal), agent_position)];
    var came_from : map<Point, Point> := map[];
    var g_score   : map<Point, int>   := map[agent_position := 0];
    // visited plays the role of the closed set.
    var visited   := new bool[grid.Length0, grid.Length1]((i, j) => false);

    // Conservative iteration budget. The open set may contain duplicates, so we use
    // a quadratic bound rather than one based only on the number of cells.
    var cell_count := grid.Length0 * grid.Length1;
    var limit      := cell_count * (cell_count + 1) + 1;
    var infinity   := limit + 1;
    var iter       := 0;

    while |open_set| > 0 && iter < limit
      invariant iter <= limit
      invariant agent_position in g_score && g_score[agent_position] == 0
      invariant forall p :: p in g_score ==> 0 <= g_score[p]
      invariant forall p :: p in g_score ==> WalkablePoint(p, grid, traversable)
      invariant forall p :: p in g_score && p != agent_position ==> p in came_from
      invariant forall p :: p in came_from ==> p in g_score && came_from[p] in g_score
      invariant forall p :: p in came_from ==> Adjacent(came_from[p], p)
      invariant forall p :: p in came_from ==> g_score[came_from[p]] + 1 == g_score[p]
      invariant forall p :: p in came_from ==> visited[came_from[p].x, came_from[p].y]
      invariant forall k :: 0 <= k < |open_set| ==> open_set[k].1 in g_score
      decreases limit - iter
    {
      iter := iter + 1;

      // Pop the node with the lowest f-score.
      var min_idx := FindMin(open_set);
      var current := open_set[min_idx].1;
      open_set := open_set[..min_idx] + open_set[min_idx + 1..];

      // Lazy deletion: skip nodes already finalized.
      if visited[current.x, current.y] {
        // Nothing to do; the outer decreases still decreases because iter grew.
      } else {
        // Goal test.
        if current == goal {
          path := ReconstructPath(came_from, g_score, agent_position, current, grid, traversable);
          FeasiblePathHasWalkablePoints(path, agent_position, current, grid, traversable);
          return;
        }

        visited[current.x, current.y] := true;

        // Relax edges to each passable neighbor.
        var neighbors := GetNeighbors(grid, current, traversable);
        var current_g := g_score[current];

        var ni := 0;
        while ni < |neighbors|
          invariant ni <= |neighbors|
          invariant current in g_score && current_g == g_score[current]
          invariant agent_position in g_score && g_score[agent_position] == 0
          invariant forall p :: p in g_score ==> 0 <= g_score[p]
          invariant forall p :: p in g_score ==> WalkablePoint(p, grid, traversable)
          invariant forall p :: p in g_score && p != agent_position ==> p in came_from
          invariant forall p :: p in came_from ==> p in g_score && came_from[p] in g_score
          invariant forall p :: p in came_from ==> Adjacent(came_from[p], p)
          invariant forall p :: p in came_from ==> g_score[came_from[p]] + 1 == g_score[p]
          invariant forall p :: p in came_from ==> visited[came_from[p].x, came_from[p].y]
          invariant forall k :: 0 <= k < |open_set| ==> open_set[k].1 in g_score
        {
          var neighbor := neighbors[ni];
          ni := ni + 1;

          assert WalkablePoint(neighbor, grid, traversable);
          if !visited[neighbor.x, neighbor.y] {
            var tentative_g := current_g + 1;
            var neighbor_g  := if neighbor in g_score then g_score[neighbor] else infinity;

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

    // No path found within the search budget.
    path := [];
  }
}
