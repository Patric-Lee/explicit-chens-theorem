import PlattPointSubsetKernel
import PlattPointPackets.S1B000218
import PlattPointPackets.S1B000219
import PlattPointPackets.S1B000220
import PlattGlobalGrid.S5B000073
namespace ChenEffective.PlattWindow.PointCovers.S5B000073
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000218.points ++ ChenEffective.PlattWindow.PointPackets.S1B000219.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000220.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000073.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000073.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000073
