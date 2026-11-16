import PlattPointSubsetKernel
import PlattPointPackets.S1B000513
import PlattPointPackets.S1B000514
import PlattPointPackets.S1B000515
import PlattPointPackets.S1B000516
import PlattPointPackets.S1B000517
import PlattGlobalGrid.S6B000069
namespace ChenEffective.PlattWindow.PointCovers.S6B000069
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000513.points ++ ChenEffective.PlattWindow.PointPackets.S1B000514.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000515.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000516.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000517.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000069.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000069.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000069
