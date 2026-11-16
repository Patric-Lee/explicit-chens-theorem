import PlattPointSubsetKernel
import PlattPointPackets.S4B000211
import PlattPointPackets.S4B000212
import PlattPointPackets.S4B000213
import PlattPointPackets.S4B000214
import PlattPointPackets.S4B000215
import PlattPointPackets.S4B000216
import PlattPointPackets.S4B000217
import PlattPointPackets.S4B000218
import PlattPointPackets.S4B000219
import PlattPointPackets.S4B000220
import PlattPointPackets.S4B000221
import PlattGlobalGrid.S8B000026
namespace ChenEffective.PlattWindow.PointCovers.S8B000026
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S4B000211.points ++ ChenEffective.PlattWindow.PointPackets.S4B000212.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000213.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000214.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000215.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000216.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000217.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000218.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000219.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000220.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000221.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000026.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000026.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000026
