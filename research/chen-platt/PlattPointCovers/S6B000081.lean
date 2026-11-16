import PlattPointSubsetKernel
import PlattPointPackets.S1B000563
import PlattPointPackets.S1B000564
import PlattPointPackets.S1B000565
import PlattPointPackets.S1B000566
import PlattPointPackets.S1B000567
import PlattPointPackets.S1B000568
import PlattGlobalGrid.S6B000081
namespace ChenEffective.PlattWindow.PointCovers.S6B000081
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000563.points ++ ChenEffective.PlattWindow.PointPackets.S1B000564.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000565.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000566.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000567.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000568.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000081.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000081.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000081
