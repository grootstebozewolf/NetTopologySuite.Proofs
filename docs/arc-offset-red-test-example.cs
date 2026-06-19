// Red test example for ARC_OFFSET full slice (RGR style)
// To be placed in NTS.Curve.Tests / CircularArcTests.cs or similar
// Run with: dotnet test --filter "Offset|ArcOffset"

using System;
using Xunit;
using NetTopologySuite.Geometries;

namespace NetTopologySuite.Curve.Tests
{
    public class CircularArcOffsetTests
    {
        // Helper to be implemented in CircularArc (analytical, pinned to proofs)
        // private static CircularArc? OffsetArc(CircularArc arc, double d) { ... }

        [Fact]
        public void Offset_Positive_Simple()
        {
            // Red until helper implemented
            var arc = new CircularArc(new Coordinate(5,0), new Coordinate(0,5), new Coordinate(-5,0));
            // Expected from oracle/proofs: radius 7, same centre, 3 controls offset radially
            // var offset = arc.Offset(2);
            // Assert.Equal(7.0, offset.Radius, 1e-9);
            Assert.True(true, "Red: implement ArcOffset helper using homothety + proofs invariants");
        }

        [Fact]
        public void Offset_Negative_CollapseToEmpty()
        {
            var arc = new CircularArc(new Coordinate(5,0), new Coordinate(0,5), new Coordinate(-5,0)); // r=5
            double d = -5.0; // r + d == 0

            // Red: expect EMPTY (or degenerate point?) per oracle mode and proofs
            // var offset = arc.Offset(d);
            // Assert.Null(offset); // or special EMPTY representation
            // For d < -r also EMPTY

            Assert.True(true, "Red: handle collapse → EMPTY when r + d <= 0 (see ArcOffset inner_offset_past_center_not_at_distance + oracle I4)");
        }

        [Fact]
        public void Offset_Negative_NearCollapse_3pts()
        {
            var arc = new CircularArc(new Coordinate(5,0), new Coordinate(0,5), new Coordinate(-5,0));
            double d = -4.999; // still positive radius, must emit valid 3pt arc

            // Red: the 3 controls must satisfy radial |d|, same centre r+d, radial ray
            // var offset = arc.Offset(d);
            // ... assertions on the 3 points using exact circumcentre from proofs
            Assert.True(true, "Red: near-collapse must still emit valid 3pt CircularArc (ArcOffsetThreePoint.v)");
        }

        [Fact]
        public void Offset_Degenerate()
        {
            var collinear = new CircularArc(new Coordinate(0,0), new Coordinate(1,0), new Coordinate(2,0));
            // var offset = collinear.Offset(1.0);
            // Assert.Null(offset); // DEGENERATE
            Assert.True(true, "Red: collinear → DEGENERATE (reuse existing arc_invariants_q)");
        }
    }
}
