import PlattPointSubsetKernel
import PlattPointPackets.S7B000226
import PlattPointPackets.S7B000227
import PlattPointPackets.S7B000228
import PlattPointPackets.S7B000229
import PlattPointPackets.S7B000230
import PlattPointPackets.S7B000231
import PlattPointPackets.S7B000232
import PlattPointPackets.S7B000233
import PlattPointPackets.S7B000234
import PlattPointPackets.S7B000235
import PlattPointPackets.S7B000236
import PlattPointPackets.S7B000237
import PlattPointPackets.S7B000238
import PlattPointPackets.S7B000239
import PlattPointPackets.S7B000240
import PlattPointPackets.S7B000241
import PlattPointPackets.S7B000242
import PlattPointPackets.S7B000243
import PlattGlobalGrid.S8B000101
namespace ChenEffective.PlattWindow.PointCovers.S8B000101
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000226.points ++ ChenEffective.PlattWindow.PointPackets.S7B000227.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000228.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000229.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000230.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000231.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000232.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000233.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000234.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000235.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000236.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000237.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000238.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000239.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000240.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000241.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000242.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000243.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000101.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000101.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000101
