import PlattPointSubsetKernel
import PlattPointPackets.S2B000012
import PlattPointPackets.S2B000013
import PlattPointPackets.S2B000014
import PlattPointPackets.S2B000015
import PlattGlobalGrid.S6B000104
namespace ChenEffective.PlattWindow.PointCovers.S6B000104
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000012.points ++ ChenEffective.PlattWindow.PointPackets.S2B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000015.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000104.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000104.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000104
