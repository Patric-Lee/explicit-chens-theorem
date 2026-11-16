import PlattPointSubsetKernel
import PlattPointPackets.S1B000145
import PlattPointPackets.S1B000146
import PlattGlobalGrid.S5B000016
namespace ChenEffective.PlattWindow.PointCovers.S5B000016
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000145.points ++ ChenEffective.PlattWindow.PointPackets.S1B000146.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S5B000016.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S5B000016.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S5B000016
