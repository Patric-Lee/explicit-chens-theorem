import PlattPointSubsetKernel
import PlattPointPackets.S1B000087
import PlattPointPackets.S1B000088
import PlattGlobalGrid.S4B000056
namespace ChenEffective.PlattWindow.PointCovers.S4B000056
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (ChenEffective.PlattWindow.PointPackets.S1B000087.points ++ ChenEffective.PlattWindow.PointPackets.S1B000088.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S4B000056.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S4B000056.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S4B000056
