import PlattPointSubsetKernel
import PlattPointPackets.S4B000033
import PlattPointPackets.S4B000034
import PlattPointPackets.S4B000035
import PlattPointPackets.S4B000036
import PlattPointPackets.S4B000037
import PlattPointPackets.S4B000038
import PlattPointPackets.S4B000039
import PlattPointPackets.S4B000040
import PlattGlobalGrid.S8B000005
namespace ChenEffective.PlattWindow.PointCovers.S8B000005
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((ChenEffective.PlattWindow.PointPackets.S4B000033.points ++ ChenEffective.PlattWindow.PointPackets.S4B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000036.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000037.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000038.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000039.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000040.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000005.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000005.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000005
