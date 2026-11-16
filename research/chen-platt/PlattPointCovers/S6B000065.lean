import PlattPointSubsetKernel
import PlattPointPackets.S1B000498
import PlattPointPackets.S1B000499
import PlattPointPackets.S1B000500
import PlattPointPackets.S1B000501
import PlattGlobalGrid.S6B000065
namespace ChenEffective.PlattWindow.PointCovers.S6B000065
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000498.points ++ ChenEffective.PlattWindow.PointPackets.S1B000499.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000500.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000501.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000065.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000065.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000065
