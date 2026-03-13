include "utils.dfy"

module Visibility{
  import opened Utils

  // -----------------------------------------------------------------------------
  // Grid-based visibility (Rectangle-Based FOV) + pathfinding skeleton
  //
  // This implements the *base* Rectangle-Based FOV idea from:
  //   Evan R.M. Debenham and Roberto Solis-Oba,
  //   "New Algorithms for Computing Field of Vision over 2D Grids" (2020)
  //
  // Notes about this implementation:
  //  * We implement the core Rectangle FOV idea from Section 2 of the paper.
  //  * We DO NOT implement the quadtree acceleration (Section 2.1/2.4) or the
  //    shrinking optimization (Section 2.3). Those are performance optimizations.
  //  * We DO implement the *adjacent-rectangle extension* idea (Section 2.2),
  //    because it affects correctness when two rectangles share a side.
  // ------------------------------------------ -----------------------------------

  function PointOnRectBoundary(p: Point, r: Rectangle): bool
  {
    p.x >= r.minX && p.x < r.maxX &&
    p.y >= r.minY && p.y < r.maxY &&
    (p.x == r.minX || p.x == r.maxX - 1 || p.y == r.minY || p.y == r.maxY - 1)
  }

  function CellInRect(x: int, y: int, r: Rectangle): bool
  {
    r.minX <= x && x < r.maxX && r.minY <= y && y < r.maxY
  }

  // Clamp an int to [lo, hi]
  function ClampInt(v: int, lo: int, hi: int): int
  {
    if v < lo then lo else if v > hi then hi else v
  }

  // ----------------------------
  // Geometry: segment vs rectangle interior intersection
  // ----------------------------
  // Returns true iff the segment from s to p intersects the *open interior* of r.
  //
  // Using open interior is important for the paper's visibility definition:
  // boundary rays are considered visible, so a segment that only touches the
  // rectangle boundary (edge or corner) should NOT be treated as blocked.
  //
  // This is the classic "slab" algorithm adapted for an OPEN axis-aligned box.
  // -----------------------------------------------------------------------------
  method SegmentIntersectsRectInterior(s: Point, p: Point, r: Rectangle) returns (hit: bool)
  {
    hit := false;

    var tEnter: real := 0.0;
    var tExit: real := 1.0;

    var dx: int := p.x - s.x;
    var dy: int := p.y - s.y;

    // X slab: r.minX < x(t) < r.maxX
    if dx == 0 {
      // Horizontal line: only intersects interior if x is strictly inside slab
      if !(s.x >= r.minX && s.x < r.maxX) {
        return;
      }
    } else {
      var tx1: real := (r.minX as real - s.x as real) / (dx as real);
      var tx2: real := (r.maxX as real - s.x as real) / (dx as real);
      var tMinX: real := if tx1 < tx2 then tx1 else tx2;
      var tMaxX: real := if tx1 > tx2 then tx1 else tx2;

      if tMinX > tEnter { tEnter := tMinX; }
      if tMaxX < tExit  { tExit  := tMaxX; }

      if tEnter >= tExit {
        return;
      }
    }

    // Y slab: r.minY < y(t) < r.maxY
    if dy == 0 {
      // Vertical line: only intersects interior if y is strictly inside slab
      if !(s.y >= r.minY && s.y < r.maxY) {
        return;
      }
    } else {
      var ty1: real := (r.minY as real - s.y as real) / (dy as real);
      var ty2: real := (r.maxY as real - s.y as real) / (dy as real);
      var tMinY: real := if ty1 < ty2 then ty1 else ty2;
      var tMaxY: real := if ty1 > ty2 then ty1 else ty2;

      if tMinY > tEnter { tEnter := tMinY; }
      if tMaxY < tExit  { tExit  := tMaxY; }

      if tEnter >= tExit {
        return;
      }
    }

    // Intersect with the segment parameter range (0,1).
    // We treat endpoints as NOT being in the interior (open).
    var t0: real := if tEnter > 0.0 then tEnter else 0.0;
    var t1: real := if tExit < 1.0 then tExit else 1.0;

    if t0 < t1 {
      hit := true;
    }
  }

  // ----------------------------
  // Choosing "relevant" rectangle vertices (paper Section 2.1)
  // ----------------------------
  // For an axis-aligned rectangle and a point source outside it, the two tangent
  // vertices are determined by the source's position relative to the rectangle.
  // These are the "relevant points" used to define the shadow wedge.
  //
  // We only need these points for the adjacency-extension step (Section 2.2).
  // For occlusion marking, we use SegmentIntersectsRectInterior directly.
  // -----------------------------------------------------------------------------
  method RelevantVertices(source: Point, rectangle: Rectangle) returns (p1: Point, p2: Point)
  {
    // Placeholder
    p1 := Point(0, 0);
    p2 := Point(0, 0);

    var N := source.x < rectangle.minX;
    var S := rectangle.maxX <= source.x;
    var W := source.y < rectangle.minY;
    var E := rectangle.maxY <= source.y;

    // source is N
    if N && !(W || E){
      p1 := Point(rectangle.minX, rectangle.minY); // top-left
      p2 := Point(rectangle.minX, rectangle.maxY); // top-right
    }

    // source is NE
    if N && E{
      p1 := Point(rectangle.minX, rectangle.minY); // top-left
      p2 := Point(rectangle.maxX, rectangle.maxY); // bottom-right
    }

    // source is E
    if E && !(N || S) {
      p1:= Point(rectangle.minX, rectangle.maxY); // top-right
      p2 := Point(rectangle.maxX, rectangle.maxY); // bottom-right
    }

    // source is SE
    if S && E{
      p1 := Point(rectangle.maxX, rectangle.minY); // bottom-left
      p2 := Point(rectangle.minX, rectangle.maxY); // top-right
    }

    // source is S
    if S && !(E || W){
      p1 := Point(rectangle.maxX, rectangle.minY); // bottom-left
      p2 := Point(rectangle.maxX, rectangle.maxY); // bottom-right
    }

    // source is SW
    if S && W{
      p1 := Point(rectangle.minX, rectangle.minY); // top-left
      p2 := Point(rectangle.maxX, rectangle.maxY); // bottom-right
    }

    // source is W
    if W && !(N || S){
      p1 := Point(rectangle.minX, rectangle.minY); // top-left
      p2 := Point(rectangle.maxX, rectangle.minY); // bottom-left
    }

    // source is NW
    if  N && W {
      p1 := Point(rectangle.maxX, rectangle.minY); // bottom-left
      p2 := Point(rectangle.minX, rectangle.maxY); // top-right
    }
  }

  // ----------------------------
  // Rectangle extension for adjacency correctness (paper Section 2.2)
  // ----------------------------
  // If two rectangles share a side, some cells behind their combined shape can be
  // invisible even if they are not "fully occluded" by either rectangle alone.
  // The paper fixes this by extending one rectangle by one row/column to overlap
  // the other rectangle at the problematic corner.
  //
  // Here we implement a safe version:
  //  * We only extend by 1 cell if the added strip is entirely Wall cells.
  //  * We extend towards a neighboring rectangle that contains the relevant vertex.
  // -----------------------------------------------------------------------------

  method CanExtendRight(grid: Grid, r: Rectangle) returns (ok: bool)
    requires ValidRectangle(r, grid)
    ensures ok ==> ValidRectangle(Rectangle(r.minX, r.minY, r.maxX, r.maxY + 1), grid)
  {
    if r.maxY == grid.Length1 {
      ok := false;
      return;
    }

    ok := true;
    for x := r.minX to r.maxX
    {
      if grid[x, r.maxY] != Wall {
        ok := false;
        return;
      }
    }
  }

  method CanExtendLeft(grid: Grid, r: Rectangle) returns (ok: bool)
    requires ValidRectangle(r, grid)
    ensures ok ==> ValidRectangle(Rectangle(r.minX, r.minY - 1, r.maxX, r.maxY), grid)
  {
    if r.minY == 0 {
      ok := false;
      return;
    }

    ok := true;
    for x := r.minX to r.maxX {
      if grid[x, r.minY - 1] != Wall {
        ok := false;
        return;
      }
    }
  }

  method CanExtendUp(grid: Grid, r: Rectangle) returns (ok: bool)
    requires ValidRectangle(r, grid)
    ensures ok ==> ValidRectangle(Rectangle(r.minX - 1, r.minY, r.maxX, r.maxY), grid)
  {
    if r.minX == 0 {
      ok := false;
      return;
    }

    ok := true;
    for y := r.minY to r.maxY {
      if grid[r.minX - 1, y] != Wall {
        ok := false;
        return;
      }
    }
  }

  method CanExtendDown(grid: Grid, r: Rectangle) returns (ok: bool)
    requires ValidRectangle(r, grid)
    ensures ok ==> ValidRectangle(Rectangle(r.minX, r.minY, r.maxX + 1, r.maxY), grid)
  {
    if r.maxX == grid.Length0 {
      ok := false;
      return;
    }

    ok := true;
    for y := r.minY to r.maxY {
      if grid[r.maxX, y] != Wall {
        ok := false;
        return;
      }
    }
  }

  method ExtendRectangleAtPoint(grid: Grid, source: Point, rectangles: array<Rectangle>, idx: int, current: Rectangle, p: Point)
    returns (outR: Rectangle)
    requires ValidRectangle(current, grid)
    requires forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
    ensures ValidRectangle(outR, grid)
  {
    outR := current;

    // Look for any other rectangle that contains this relevant point.
    for j := 0 to rectangles.Length
      invariant ValidRectangle(outR, grid)
    {
      if j != idx && PointOnRectBoundary(p, rectangles[j]) {
        // If rectangles[j] does NOT occlude p, extend current to overlap rectangles[j].
        var point := Point(p.x, p.y);
        var occludes := SegmentIntersectsRectInterior(source, point, rectangles[j]);
        // Try extending across the side shared with rectangles[j] that contains p.
        if !occludes {
          // Right adjacency
          if rectangles[j].minY == outR.maxY && p.y == outR.maxY {
            var can := CanExtendRight(grid, outR);
            if can {
              outR := Rectangle(outR.minX, outR.minY, outR.maxX, outR.maxY + 1);
            }
          }
          // Left adjacency
          if rectangles[j].maxY == outR.minY && p.y == outR.minY {
            var can := CanExtendLeft(grid, outR);
            if can {
              outR := Rectangle(outR.minX, outR.minY - 1, outR.maxX, outR.maxY);
            }
          }
          // Up adjacency
          if rectangles[j].minX == outR.maxX && p.x == outR.maxX {
            var can := CanExtendUp(grid, outR);
            if can {
              outR := Rectangle(outR.minX - 1, outR.minY, outR.maxX, outR.maxY);
            }
          }
          // Down adjacency
          if rectangles[j].maxX == outR.minX && p.x == outR.minX {
            var can := CanExtendDown(grid, outR);
            if can {
              outR := Rectangle(outR.minX, outR.minY, outR.maxX + 1, outR.maxY);
            }
          }
        }
      }
    }
  }

  method ExtendRectangleIfNeeded(grid: Grid, source: Point, rectangles: array<Rectangle>, idx: int) returns (rOut: Rectangle)
    requires 0 <= idx < rectangles.Length
    requires forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
    ensures ValidRectangle(rOut, grid)
  {
    rOut := rectangles[idx];

    // Do a small fixed number of refinement iterations. Extension is at most 1 cell per relevant point, so 2 iterations is enough for this baseline.
    for iter := 0 to 2
      invariant ValidRectangle(rOut, grid)
    {
      var before := rOut;
      var p1, p2 := RelevantVertices(source, rOut);

      rOut := ExtendRectangleAtPoint(grid, source, rectangles, idx, rOut, p1);
      rOut := ExtendRectangleAtPoint(grid, source, rectangles, idx, rOut, p2);

      if rOut == before {
        break;
      }
    }
  }

  // ----------------------------
  // Cell occlusion test (single rectangle)
  // ----------------------------
  // A cell is treated as "not visible" from the source if it is *entirely*
  // occluded. For a convex occluded region, it's enough to check the 4 corners.
  //
  // We exclude cells that are part of the blocking rectangle itself (those cells
  // are typically visible as walls).
  // -----------------------------------------------------------------------------
  method IsCellOccludedByRect(source: Point, x: int, y: int, r: Rectangle) returns (occluded: bool)
  {
    if CellInRect(x, y, r) {
      occluded := false;
      return;
    }

    var c1 := Point(x, y);
    var c2 := Point(x + 1, y);
    var c3 := Point(x, y + 1);
    var c4 := Point(x + 1, y + 1);

    var h1: bool;
    var h2: bool;
    var h3: bool;
    var h4: bool;
    h1 := SegmentIntersectsRectInterior(source, c1, r);
    h2 := SegmentIntersectsRectInterior(source, c2, r);
    h3 := SegmentIntersectsRectInterior(source, c3, r);
    h4 := SegmentIntersectsRectInterior(source, c4, r);

    occluded := h1 && h2 && h3 && h4;
  }

  method RectangleFOV(grid: Grid, rectangles_in: array<Rectangle>, source: Point) returns (visible: array2<bool>)
    requires ValidPoint(source, grid)
    requires forall j :: 0 <= j < rectangles_in.Length ==> ValidRectangle(rectangles_in[j], grid)
    ensures visible.Length0 == grid.Length0 && visible.Length1 == grid.Length1
  {
    var rectangles := new Rectangle[rectangles_in.Length] (i requires 0 <= i < rectangles_in.Length reads rectangles_in => rectangles_in[i]);

    visible := new bool[grid.Length0, grid.Length1] ((i, j) => (true));

    // Process rectangles one-by-one.
    for i := 0 to rectangles.Length
      invariant forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
    {
      var r := ExtendRectangleIfNeeded(grid, source, rectangles, i);
      rectangles[i] := r;

      for x := 0 to grid.Length0
        invariant forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid) // This is stupid dafny should recognize that these loops don't modify rectangles
      {
        for y := 0 to grid.Length1
          invariant forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)  // This is stupid dafny should recognize that these loops don't modify rectangles
        {
          if visible[x, y] {
            var occ := IsCellOccludedByRect(source, x, y, r);
            if occ {
              visible[x, y] := false;
            }
          }
        }
      }
    }

    visible[source.x, source.y] := true;
  }

  method GetVisibleGoals(grid: Grid, rectangles: array<Rectangle>, agent_position: Point, value_function: Cell -> real)
    returns (visible_goals: seq<Point>)
    requires ValidPoint(agent_position, grid)
    requires forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)
    requires RectanglesMatchGrid(rectangles, grid)
  {
    visible_goals := [];
    var visible := RectangleFOV(grid, rectangles, agent_position);

    for x := 0 to grid.Length0 {
      for y := 0 to grid.Length1{
        var c := grid[x, y];
        if visible[x, y] && value_function(c) > 0.0 {
          // Return cell centers as goal positions
          visible_goals := visible_goals + [Point(x, y)];
        }
      }
    }
  }
}