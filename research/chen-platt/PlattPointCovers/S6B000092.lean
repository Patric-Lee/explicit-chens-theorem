import PlattPointSubsetKernel
import PlattPointPackets.S1B000614
import PlattPointPackets.S1B000615
import PlattPointPackets.S1B000616
import PlattPointPackets.S1B000617
import PlattPointPackets.S1B000618
import PlattPointPackets.S1B000619
import PlattGlobalGrid.S6B000092
namespace ChenEffective.PlattWindow.PointCovers.S6B000092
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000614.points ++ ChenEffective.PlattWindow.PointPackets.S1B000615.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000616.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000617.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000618.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000619.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000092.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000092.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000092
