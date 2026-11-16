import PlattPointSubsetKernel
import PlattPointPackets.S7B000209
import PlattPointPackets.S7B000210
import PlattPointPackets.S7B000211
import PlattPointPackets.S7B000212
import PlattPointPackets.S7B000213
import PlattPointPackets.S7B000214
import PlattPointPackets.S7B000215
import PlattPointPackets.S7B000216
import PlattPointPackets.S7B000217
import PlattPointPackets.S7B000218
import PlattPointPackets.S7B000219
import PlattPointPackets.S7B000220
import PlattPointPackets.S7B000221
import PlattPointPackets.S7B000222
import PlattPointPackets.S7B000223
import PlattPointPackets.S7B000224
import PlattPointPackets.S7B000225
import PlattPointPackets.S7B000226
import PlattGlobalGrid.S8B000100
namespace ChenEffective.PlattWindow.PointCovers.S8B000100
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000209.points ++ ChenEffective.PlattWindow.PointPackets.S7B000210.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000211.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000212.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000213.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000214.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000215.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000216.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000217.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000218.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000219.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000220.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000221.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000222.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000223.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000224.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000225.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000226.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000100.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000100.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000100
