import PlattPointSubsetKernel
import PlattPointPackets.S1B000404
import PlattPointPackets.S1B000405
import PlattPointPackets.S1B000406
import PlattPointPackets.S1B000407
import PlattGlobalGrid.S6B000038
namespace ChenEffective.PlattWindow.PointCovers.S6B000038
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000404.points ++ ChenEffective.PlattWindow.PointPackets.S1B000405.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000406.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000407.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000038.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000038.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000038
