import PlattPointSubsetKernel
import PlattPointPackets.S2B000010
import PlattPointPackets.S2B000011
import PlattPointPackets.S2B000012
import PlattGlobalGrid.S6B000103
namespace ChenEffective.PlattWindow.PointCovers.S6B000103
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S2B000010.points ++ ChenEffective.PlattWindow.PointPackets.S2B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000012.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000103.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000103.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000103
