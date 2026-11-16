import PlattPointSubsetKernel
import PlattPointPackets.S1B000604
import PlattPointPackets.S1B000605
import PlattPointPackets.S1B000606
import PlattPointPackets.S1B000607
import PlattPointPackets.S1B000608
import PlattPointPackets.S1B000609
import PlattGlobalGrid.S6B000090
namespace ChenEffective.PlattWindow.PointCovers.S6B000090
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000604.points ++ ChenEffective.PlattWindow.PointPackets.S1B000605.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000606.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000607.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000608.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000609.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000090.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000090.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000090
