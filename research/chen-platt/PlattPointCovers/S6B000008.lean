import PlattPointSubsetKernel
import PlattPointPackets.S1B000322
import PlattPointPackets.S1B000323
import PlattPointPackets.S1B000324
import PlattGlobalGrid.S6B000008
namespace ChenEffective.PlattWindow.PointCovers.S6B000008
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000322.points ++ ChenEffective.PlattWindow.PointPackets.S1B000323.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000324.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000008.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000008.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000008
