// ----------------------------------------------------------------------------------
// Grid-based visibility (Rectangle-Based FOV) from:
//   Evan R.M. Debenham and Roberto Solis-Oba,
//   "New Algorithms for Computing Field of Vision over 2D Grids" (2020)
// https://aircconline.com/csit/papers/vol10/csit101801.pdf
// 
// Notes:
// We have only implemented base rectangle FOV
// Didn't implement the quadtree or FOV update optimizations.
// ----------------------------------------------------------------------------------

include "utils.dfy"
module Visibility{
  import opened Utils

  function PointOnRectBoundary(p: Point, r: Rectangle): bool
  {
    p.x >= r.minX && p.x < r.maxX &&
    p.y >= r.minY && p.y < r.maxY &&
    (p.x == r.minX || p.x == r.maxX - 1 || p.y == r.minY || p.y == r.maxY - 1)
  }

  method DistanceSquared(p1: Point, p2: Point) returns (distance: int)
  {
    var dx := p1.x - p2.x;
    var dy := p1.y - p2.y;
    distance := dx * dx + dy * dy;
  }

  // Check if a line segment from s to p intersects the interior of rectangle r.
  // Rectangle is treated as (open) meaning a ray that passes through the boundary but does not enter the interior is NOT considered an intersection.
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

  // Get the two relevant vertices of rectangle r with respect to source point.
  // Relevant vertices are defined as the two farthest apart visible corners from the source.
  method RelevantVertices(source: Point, rectangle: Rectangle) returns (p1: Point, p2: Point)
  {
    var corner1 := Point(rectangle.minX, rectangle.minY); // top-left
    var corner2 := Point(rectangle.maxX, rectangle.minY); // top-right
    var corner3 := Point(rectangle.minX, rectangle.maxY); // bottom-left
    var corner4 := Point(rectangle.maxX, rectangle.maxY); // bottom-right

    var c1_occluded := SegmentIntersectsRectInterior(source, corner1, rectangle);
    var c2_occluded := SegmentIntersectsRectInterior(source, corner2, rectangle);
    var c3_occluded := SegmentIntersectsRectInterior(source, corner3, rectangle);
    var c4_occluded := SegmentIntersectsRectInterior(source, corner4, rectangle);

    var visible_corners := [];
    if !c1_occluded { visible_corners := visible_corners + [corner1]; }
    if !c2_occluded { visible_corners := visible_corners + [corner2]; }
    if !c3_occluded { visible_corners := visible_corners + [corner3]; }
    if !c4_occluded { visible_corners := visible_corners + [corner4]; }

    // Find the farthest pair of visible corners. This is guaranteed to be the correct pair of tangent vertices.
    var max_dist := -1;
    p1 := corner1; // dummy init to satisfy dafny
    p2 := corner1; // dummy init to satisfy dafny
    for i := 0 to |visible_corners| {
      for j := i + 1 to |visible_corners| {
        var d := DistanceSquared(visible_corners[i], visible_corners[j]);
        if d > max_dist {
          max_dist := d;
          p1 := visible_corners[i];
          p2 := visible_corners[j];
        }
      }
    }
  }

  // Check if a single cell (x,y) is occluded by rectangle r with respect to source point.
  // Cells are occluded if at least 3 corners are occluded by r.
  method CellOccludedByRect(source: Point, x: int, y: int, r: Rectangle) returns (occluded: bool)
  {
    var c1 := Point(x, y);
    var c2 := Point(x + 1, y);
    var c3 := Point(x, y + 1);
    var c4 := Point(x + 1, y + 1);

    var h1 := SegmentIntersectsRectInterior(source, c1, r);
    var h2 := SegmentIntersectsRectInterior(source, c2, r);
    var h3 := SegmentIntersectsRectInterior(source, c3, r);
    var h4 := SegmentIntersectsRectInterior(source, c4, r);

    var num_occluded := 0;
    if h1 { num_occluded := num_occluded + 1; }
    if h2 { num_occluded := num_occluded + 1; }
    if h3 { num_occluded := num_occluded + 1; }
    if h4 { num_occluded := num_occluded + 1; }

    occluded := num_occluded >= 3;
  }

  method CalculateFOV(grid: Grid, rectangles_in: array<Rectangle>, source: Point) returns (visible: array2<bool>)
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
      for x := 0 to grid.Length0
        invariant forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid) // This is stupid dafny should recognize that these loops don't modify rectangles
      {
        for y := 0 to grid.Length1
          invariant forall j :: 0 <= j < rectangles.Length ==> ValidRectangle(rectangles[j], grid)  // This is stupid dafny should recognize that these loops don't modify rectangles
        {
          if visible[x, y] {
            var occ := CellOccludedByRect(source, x, y, rectangles[i]);
            if occ {
              visible[x, y] := false;
            }
          }
        }
      }
    }

    visible[source.x, source.y] := true;
  }
}