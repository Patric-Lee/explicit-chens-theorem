import PlattPointSubsetKernel
import PlattPointPackets.S1B000317
import PlattPointPackets.S1B000318
import PlattPointPackets.S1B000319
import PlattGlobalGrid.S6B000006
namespace ChenEffective.PlattWindow.PointCovers.S6B000006
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000317.points ++ ChenEffective.PlattWindow.PointPackets.S1B000318.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000319.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000006.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000006.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000006
