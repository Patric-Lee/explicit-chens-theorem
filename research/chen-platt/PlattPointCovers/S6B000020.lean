import PlattPointSubsetKernel
import PlattPointPackets.S1B000353
import PlattPointPackets.S1B000354
import PlattPointPackets.S1B000355
import PlattGlobalGrid.S6B000020
namespace ChenEffective.PlattWindow.PointCovers.S6B000020
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000353.points ++ ChenEffective.PlattWindow.PointPackets.S1B000354.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000355.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000020.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000020.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000020
