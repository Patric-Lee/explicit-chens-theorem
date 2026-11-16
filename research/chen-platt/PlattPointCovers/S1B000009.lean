import PlattPointSubsetKernel
import PlattPointPackets.S1B000000
import PlattGlobalGrid.S1B000009
namespace ChenEffective.PlattWindow.PointCovers.S1B000009
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ChenEffective.PlattWindow.PointPackets.S1B000000.points
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S1B000009.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S1B000009.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S1B000009
