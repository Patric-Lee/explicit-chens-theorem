import PlattPointSubsetKernel
import PlattPointPackets.S1B000249
import PlattPointPackets.S1B000250
import PlattPointPackets.S1B000251
import PlattGlobalGrid.S5B000091
namespace ChenEffective.PlattWindow.PointCovers.S5B000091
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((ChenEffective.PlattWindow.PointPackets.S1B000249.points ++ ChenEffective.PlattWindow.PointPackets.S1B000250.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000251.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000091.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000091.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000091
