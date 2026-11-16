import PlattPointSubsetKernel
import PlattPointPackets.S1B000361
import PlattPointPackets.S1B000362
import PlattPointPackets.S1B000363
import PlattGlobalGrid.S6B000023
namespace ChenEffective.PlattWindow.PointCovers.S6B000023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000361.points ++ ChenEffective.PlattWindow.PointPackets.S1B000362.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000363.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000023.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000023.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000023
