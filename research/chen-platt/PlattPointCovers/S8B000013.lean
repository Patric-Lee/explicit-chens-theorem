import PlattPointSubsetKernel
import PlattPointPackets.S4B000097
import PlattPointPackets.S4B000098
import PlattPointPackets.S4B000099
import PlattPointPackets.S4B000100
import PlattPointPackets.S4B000101
import PlattPointPackets.S4B000102
import PlattPointPackets.S4B000103
import PlattPointPackets.S4B000104
import PlattPointPackets.S4B000105
import PlattGlobalGrid.S8B000013
namespace ChenEffective.PlattWindow.PointCovers.S8B000013
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S4B000097.points ++ ChenEffective.PlattWindow.PointPackets.S4B000098.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000099.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000100.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000101.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000102.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000103.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000104.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000105.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000013.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000013.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000013
