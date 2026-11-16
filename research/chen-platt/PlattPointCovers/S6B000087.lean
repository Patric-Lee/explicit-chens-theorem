import PlattPointSubsetKernel
import PlattPointPackets.S1B000590
import PlattPointPackets.S1B000591
import PlattPointPackets.S1B000592
import PlattPointPackets.S1B000593
import PlattPointPackets.S1B000594
import PlattPointPackets.S1B000595
import PlattGlobalGrid.S6B000087
namespace ChenEffective.PlattWindow.PointCovers.S6B000087
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000590.points ++ ChenEffective.PlattWindow.PointPackets.S1B000591.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000592.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000593.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000594.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000595.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000087.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000087.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000087
