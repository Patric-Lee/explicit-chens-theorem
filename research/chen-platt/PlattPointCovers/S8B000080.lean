import PlattPointSubsetKernel
import PlattPointPackets.S6B000212
import PlattPointPackets.S6B000213
import PlattPointPackets.S6B000214
import PlattPointPackets.S6B000215
import PlattPointPackets.S6B000216
import PlattPointPackets.S6B000217
import PlattPointPackets.S6B000218
import PlattPointPackets.S6B000219
import PlattPointPackets.S6B000220
import PlattPointPackets.S6B000221
import PlattPointPackets.S6B000222
import PlattPointPackets.S6B000223
import PlattPointPackets.S6B000224
import PlattPointPackets.S6B000225
import PlattPointPackets.S6B000226
import PlattPointPackets.S6B000227
import PlattGlobalGrid.S8B000080
namespace ChenEffective.PlattWindow.PointCovers.S8B000080
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000212.points ++ ChenEffective.PlattWindow.PointPackets.S6B000213.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000214.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000215.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000216.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000217.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000218.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000219.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000220.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000221.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000222.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000223.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000224.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000225.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000226.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000227.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000080.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000080.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000080
