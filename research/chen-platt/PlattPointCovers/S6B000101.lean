import PlattPointSubsetKernel
import PlattPointPackets.S2B000005
import PlattPointPackets.S2B000006
import PlattPointPackets.S2B000007
import PlattGlobalGrid.S6B000101
namespace ChenEffective.PlattWindow.PointCovers.S6B000101
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S2B000005.points ++ ChenEffective.PlattWindow.PointPackets.S2B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000007.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000101.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000101.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000101
