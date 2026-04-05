// ----------------------------------------------------------------------------------
// array2<T>-based visibility (Rectangle-Based FOV) from:
//   Evan R.M. Debenham and Roberto Solis-Oba,
//   "New Algorithms for Computing Field of Vision over 2D grids" (2020)
// https://aircconline.com/csit/papers/vol10/csit101801.pdf
//
// Notes:
// We have only implemented base rectangle FOV.
// Didn't implement the quadtree or FOV update optimizations.
//
// Coordinate convention:
// All geometric ray tests use the "doubling trick": every grid coordinate is
// multiplied by 2 so that the center of cell (x,y) sits at the integer point
// (2x+1, 2y+1), and every cell corner sits at an even integer point. This lets
// us shoot rays from the exact center of the source cell using only integer
// arithmetic throughout.
// ----------------------------------------------------------------------------------

include "utils.dfy"
module Visibility {
  import opened Utils

  // --------------------------------------------------------------------------
  // Small helper definitions used by both the executable code and the proofs.
  // --------------------------------------------------------------------------

  function MinReal(a: real, b: real): real {
    if a < b then a else b
  }

  function MaxReal(a: real, b: real): real {
    if a > b then a else b
  }

  function CountTrue4(b1: bool, b2: bool, b3: bool, b4: bool): int {
    (if b1 then 1 else 0) +
    (if b2 then 1 else 0) +
    (if b3 then 1 else 0) +
    (if b4 then 1 else 0)
  }

  ghost predicate IsRectangleCorner(p: Point, r: Rectangle) {
    p == Point(r.minX, r.minY) ||
    p == Point(r.maxX, r.minY) ||
    p == Point(r.minX, r.maxY) ||
    p == Point(r.maxX, r.maxY)
  }

  // --------------------------------------------------------------------------
  // Doubled-coordinate helpers
  // --------------------------------------------------------------------------

  // Center of cell p in the doubled coordinate space.
  // Cell (x,y) spans [2x, 2x+2] x [2y, 2y+2], so its center is (2x+1, 2y+1).
  function CellCenterDoubled(p: Point): Point {
    Point(2 * p.x + 1, 2 * p.y + 1)
  }

  // Rectangle in doubled coordinate space.
  // Grid rectangle [minX, maxX) x [minY, maxY) becomes
  // [2*minX, 2*maxX) x [2*minY, 2*maxY).
  function RectDoubled(r: Rectangle): Rectangle {
    Rectangle(2 * r.minX, 2 * r.minY, 2 * r.maxX, 2 * r.maxY)
  }

  // --------------------------------------------------------------------------
  // Topology helpers
  // --------------------------------------------------------------------------

  // Check if a point p is on the boundary of rectangle r (regular grid coords).
  predicate PointOnRectBoundary(p: Point, r: Rectangle) {
    p.x >= r.minX && p.x <= r.maxX &&
    p.y >= r.minY && p.y <= r.maxY &&
    (p.x == r.minX || p.x == r.maxX || p.y == r.minY || p.y == r.maxY)
  }

  // --------------------------------------------------------------------------
  // Geometric predicates shared by proofs and executable code.
  // --------------------------------------------------------------------------

  // Whether the segment from s to p intersects the open interior of rectangle r.
  // A segment that only grazes the boundary is not a hit.
  predicate SegmentIntersectsRectInterior(s: Point, p: Point, r: Rectangle) {
    var dx := p.x - s.x;
    var dy := p.y - s.y;
    var xOk := dx != 0 || (s.x >= r.minX && s.x < r.maxX);
    var yOk := dy != 0 || (s.y >= r.minY && s.y < r.maxY);
    if !xOk || !yOk then
      false
    else
      var tx1 := if dx == 0 then 0.0 else (r.minX as real - s.x as real) / (dx as real);
      var tx2 := if dx == 0 then 1.0 else (r.maxX as real - s.x as real) / (dx as real);
      var ty1 := if dy == 0 then 0.0 else (r.minY as real - s.y as real) / (dy as real);
      var ty2 := if dy == 0 then 1.0 else (r.maxY as real - s.y as real) / (dy as real);
      var tEnterX := if dx == 0 then 0.0 else MinReal(tx1, tx2);
      var tExitX  := if dx == 0 then 1.0 else MaxReal(tx1, tx2);
      var tEnterY := if dy == 0 then 0.0 else MinReal(ty1, ty2);
      var tExitY  := if dy == 0 then 1.0 else MaxReal(ty1, ty2);
      var tEnter  := MaxReal(tEnterX, tEnterY);
      var tExit   := MinReal(tExitX, tExitY);
      var t0      := MaxReal(tEnter, 0.0);
      var t1      := MinReal(tExit,  1.0);
      t0 < t1
  }

  // Check whether cell (x, y) is occluded by rectangle r from source.
  // A cell is occluded when at least 3 of its 4 corners are blocked by r.
  predicate CellOccludedByRect(source: Point, x: int, y: int, r: Rectangle) {
    var src := CellCenterDoubled(source);
    var dr  := RectDoubled(r);

    var c1 := Point(2 * x,     2 * y    );
    var c2 := Point(2 * x + 2, 2 * y    );
    var c3 := Point(2 * x,     2 * y + 2);
    var c4 := Point(2 * x + 2, 2 * y + 2);

    CountTrue4(
      SegmentIntersectsRectInterior(src, c1, dr),
      SegmentIntersectsRectInterior(src, c2, dr),
      SegmentIntersectsRectInterior(src, c3, dr),
      SegmentIntersectsRectInterior(src, c4, dr)) >= 3
  }

  // A pure visibility specification for a single destination cell given an
  // ordered list of (already extended) blocking rectangles.
  //
  // The source cell is always visible, matching the final FOV result.
  ghost predicate VisibleCell(source: Point, dest: Point, rectangles: seq<Rectangle>)
    decreases |rectangles|
  {
    if dest == source then
      true
    else if |rectangles| == 0 then
      true
    else
      VisibleCell(source, dest, rectangles[..|rectangles| - 1]) &&
      !CellOccludedByRect(source, dest.x, dest.y, rectangles[|rectangles| - 1])
  }

  // --------------------------------------------------------------------------
  // Rectangle extension
  // --------------------------------------------------------------------------

  // If two rectangles share a side, cells just behind their join can be
  // incorrectly marked visible. Extend current by one cell into any adjacent
  // rectangle that does not itself occlude the relevant corner point p.
  //
  // All geometric tests are performed in the doubled coordinate space so that
  // rays originate from the exact center of the source cell.
  method ExtendRectangleAtPoint<T>(
    grid: array2<T>,
    source: Point,
    rectangles: array<Rectangle>,
    idx: int,
    current: Rectangle,
    p: Point)
    returns (outR: Rectangle)
    requires RectangleInRange(current, grid)
    requires forall j :: 0 <= j < rectangles.Length ==> RectangleInRange(rectangles[j], grid)
    ensures  RectangleInRange(outR, grid)
    ensures  RectangleContains(outR, current)
  {
    outR := current;

    var src := CellCenterDoubled(source);
    // p is a rectangle corner in regular grid coords; double it for the ray test.
    var p_d := Point(2 * p.x, 2 * p.y);

    for j := 0 to rectangles.Length
      invariant RectangleInRange(outR, grid)
      invariant RectangleContains(outR, current)
    {
      if j != idx && PointOnRectBoundary(p, rectangles[j]) {
        var rect_d   := RectDoubled(rectangles[j]);
        var occludes := SegmentIntersectsRectInterior(src, p_d, rect_d);

        if !occludes {
          if current.minX == rectangles[j].maxX {
            outR := Rectangle(current.minX - 1, current.minY, current.maxX, current.maxY);
          } else if current.maxX == rectangles[j].minX {
            outR := Rectangle(current.minX, current.minY, current.maxX + 1, current.maxY);
          } else if current.minY == rectangles[j].maxY {
            outR := Rectangle(current.minX, current.minY - 1, current.maxX, current.maxY);
          } else if current.maxY == rectangles[j].minY {
            outR := Rectangle(current.minX, current.minY, current.maxX, current.maxY + 1);
          }
        }
      }
    }
  }

  ghost predicate RectangleContains(outer: Rectangle, inner: Rectangle) {
    outer.minX <= inner.minX && outer.minY <= inner.minY &&
    inner.maxX <= outer.maxX && inner.maxY <= outer.maxY
  }

  // Return the two relevant (tangent) corners of rectangle as seen from source.
  // Relevant corners are the two visible corners with the greatest mutual distance.
  //
  // Visibility self-test uses doubled coordinates: source -> cell center,
  // corners -> even-coordinate grid points. Return values are in regular grid
  // coords because callers use them for topology checks (PointOnRectBoundary).
  method RelevantVertices(source: Point, rectangle: Rectangle) returns (p1: Point, p2: Point)
    ensures IsRectangleCorner(p1, rectangle)
    ensures IsRectangleCorner(p2, rectangle)
  {
    var src := CellCenterDoubled(source);
    var dr  := RectDoubled(rectangle);

    // Regular-grid corners (for return / topology use).
    var corner1 := Point(rectangle.minX, rectangle.minY); // top-left
    var corner2 := Point(rectangle.maxX, rectangle.minY); // top-right
    var corner3 := Point(rectangle.minX, rectangle.maxY); // bottom-left
    var corner4 := Point(rectangle.maxX, rectangle.maxY); // bottom-right

    // Doubled-coord corners (for ray intersection tests).
    var corner1_d := Point(2 * rectangle.minX, 2 * rectangle.minY);
    var corner2_d := Point(2 * rectangle.maxX, 2 * rectangle.minY);
    var corner3_d := Point(2 * rectangle.minX, 2 * rectangle.maxY);
    var corner4_d := Point(2 * rectangle.maxX, 2 * rectangle.maxY);

    var c1_occluded := SegmentIntersectsRectInterior(src, corner1_d, dr);
    var c2_occluded := SegmentIntersectsRectInterior(src, corner2_d, dr);
    var c3_occluded := SegmentIntersectsRectInterior(src, corner3_d, dr);
    var c4_occluded := SegmentIntersectsRectInterior(src, corner4_d, dr);

    var visible_corners := [];
    if !c1_occluded { visible_corners := visible_corners + [corner1]; }
    if !c2_occluded { visible_corners := visible_corners + [corner2]; }
    if !c3_occluded { visible_corners := visible_corners + [corner3]; }
    if !c4_occluded { visible_corners := visible_corners + [corner4]; }

    // The farthest-apart pair of visible corners are the tangent vertices.
    var max_dist := -1;
    p1 := corner1; // dummy inits required by Dafny
    p2 := corner1;

    for i := 0 to |visible_corners|
      invariant IsRectangleCorner(p1, rectangle)
      invariant IsRectangleCorner(p2, rectangle)
      invariant forall k :: 0 <= k < |visible_corners| ==> IsRectangleCorner(visible_corners[k], rectangle)
    {
      for j := i + 1 to |visible_corners|
        invariant IsRectangleCorner(p1, rectangle)
        invariant IsRectangleCorner(p2, rectangle)
        invariant forall k :: 0 <= k < |visible_corners| ==> IsRectangleCorner(visible_corners[k], rectangle)
      {
        var d := ManhattanDistance(visible_corners[i], visible_corners[j]);
        if d > max_dist {
          max_dist := d;
          p1 := visible_corners[i];
          p2 := visible_corners[j];
        }
      }
    }
  }

  // Extend the rectangle at idx if needed so that it properly occludes its
  // two relevant (tangent) vertices, then return the extended rectangle.
  method ExtendRectangle<T>(
    grid: array2<T>,
    source: Point,
    rectangles: array<Rectangle>,
    idx: int)
    returns (rOut: Rectangle)
    requires 0 <= idx < rectangles.Length
    requires forall j :: 0 <= j < rectangles.Length ==> RectangleInRange(rectangles[j], grid)
    ensures  RectangleInRange(rOut, grid)
    ensures  RectangleContains(rOut, rectangles[idx])
  {
    var base := rectangles[idx];
    rOut := base;
    var p1, p2 := RelevantVertices(source, rOut);
    rOut := ExtendRectangleAtPoint(grid, source, rectangles, idx, rOut, p1);
    rOut := ExtendRectangleAtPoint(grid, source, rectangles, idx, rOut, p2);
  }

  // --------------------------------------------------------------------------
  // Verified visibility accumulation over the grid.
  // --------------------------------------------------------------------------

  method ApplyRectangleToVisibility<T>(
    grid: array2<T>,
    visible: array2<bool>,
    source: Point,
    r: Rectangle,
    processed: seq<Rectangle>)
    requires grid.Length0 == visible.Length0 && grid.Length1 == visible.Length1
    requires RectangleInRange(r, grid)
    requires forall j :: 0 <= j < |processed| ==> RectangleInRange(processed[j], grid)
    requires forall x, y :: 0 <= x < grid.Length0 && 0 <= y < grid.Length1 ==>
                              visible[x, y] == VisibleCell(source, Point(x, y), processed)
    modifies visible
    ensures forall x, y :: 0 <= x < grid.Length0 && 0 <= y < grid.Length1 ==>
                             visible[x, y] == VisibleCell(source, Point(x, y), processed + [r])
  {
    for x := 0 to grid.Length0
      invariant 0 <= x <= grid.Length0
      invariant forall x0, y0 :: 0 <= x0 < x && 0 <= y0 < grid.Length1 ==>
                                   visible[x0, y0] == VisibleCell(source, Point(x0, y0), processed + [r])
      invariant forall x0, y0 :: x <= x0 < grid.Length0 && 0 <= y0 < grid.Length1 ==>
                                   visible[x0, y0] == VisibleCell(source, Point(x0, y0), processed)
    {
      for y := 0 to grid.Length1
        invariant 0 <= y <= grid.Length1
        invariant forall x0, y0 :: 0 <= x0 < x && 0 <= y0 < grid.Length1 ==>
                                     visible[x0, y0] == VisibleCell(source, Point(x0, y0), processed + [r])
        invariant forall y0 :: 0 <= y0 < y ==>
                                 visible[x, y0] == VisibleCell(source, Point(x, y0), processed + [r])
        invariant forall y0 :: y <= y0 < grid.Length1 ==>
                                 visible[x, y0] == VisibleCell(source, Point(x, y0), processed)
        invariant forall x0, y0 :: x < x0 < grid.Length0 && 0 <= y0 < grid.Length1 ==>
                                     visible[x0, y0] == VisibleCell(source, Point(x0, y0), processed)
      {
        var dest := Point(x, y);
        var occ := CellOccludedByRect(source, x, y, r);

        if dest == source {
          visible[x, y] := true;
        } else {
          var wasVisible := visible[x, y];
          visible[x, y] := wasVisible && !occ;
        }
      }
    }
  }

  // Proof-oriented entry point: returns both the visibility map and the final
  // sequence of extended rectangles that justifies it.
  method CalculateFOV<T>(grid: array2<T>, rectangles_in: array<Rectangle>, source: Point)
    returns (visible: array2<bool>, extended: seq<Rectangle>)
    requires ValidPoint(source, grid)
    requires forall j :: 0 <= j < rectangles_in.Length ==> RectangleInRange(rectangles_in[j], grid)
    ensures  visible.Length0 == grid.Length0 && visible.Length1 == grid.Length1
    ensures  visible[source.x, source.y]
    ensures  |extended| == rectangles_in.Length
    ensures  forall j :: 0 <= j < |extended| ==> RectangleInRange(extended[j], grid)
    ensures  forall j :: 0 <= j < |extended| ==> RectangleContains(extended[j], rectangles_in[j])
    ensures  forall x, y :: 0 <= x < grid.Length0 && 0 <= y < grid.Length1 ==>
                              visible[x, y] == VisibleCell(source, Point(x, y), extended)
  {
    var rectangles := new Rectangle[rectangles_in.Length](
                                    i requires 0 <= i < rectangles_in.Length reads rectangles_in => rectangles_in[i]);

    visible := new bool[grid.Length0, grid.Length1]((i, j) => true);
    extended := [];

    for i := 0 to rectangles.Length
      invariant 0 <= i <= rectangles.Length
      invariant |extended| == i
      invariant forall j :: 0 <= j < rectangles.Length ==> RectangleInRange(rectangles[j], grid)
      invariant forall j :: 0 <= j < i ==> rectangles[j] == extended[j]
      invariant forall j :: i <= j < rectangles.Length ==> rectangles[j] == rectangles_in[j]
      invariant forall j :: 0 <= j < i ==> RectangleContains(extended[j], rectangles_in[j])
      invariant forall x, y :: 0 <= x < grid.Length0 && 0 <= y < grid.Length1 ==>
                                 visible[x, y] == VisibleCell(source, Point(x, y), extended)
    {
      var r := ExtendRectangle(grid, source, rectangles, i);
      rectangles[i] := r;
      ApplyRectangleToVisibility(grid, visible, source, r, extended);
      extended := extended + [r];
    }
  }
}
