import PlattPointSubsetKernel
import PlattPointPackets.S1B000255
import PlattPointPackets.S1B000256
import PlattPointPackets.S1B000257
import PlattGlobalGrid.S5B000094
namespace ChenEffective.PlattWindow.PointCovers.S5B000094
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000255.points ++ ChenEffective.PlattWindow.PointPackets.S1B000256.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000257.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000094.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000094.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000094
