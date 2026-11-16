import PlattPointSubsetKernel
import PlattPointPackets.S2B000271
import PlattPointPackets.S2B000272
import PlattPointPackets.S2B000273
import PlattPointPackets.S2B000274
import PlattPointPackets.S2B000275
import PlattGlobalGrid.S7B000059
namespace ChenEffective.PlattWindow.PointCovers.S7B000059
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000271.points ++ ChenEffective.PlattWindow.PointPackets.S2B000272.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000273.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000274.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000275.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000059.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000059.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000059
