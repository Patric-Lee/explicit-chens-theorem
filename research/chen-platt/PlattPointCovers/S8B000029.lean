import PlattPointSubsetKernel
import PlattPointPackets.S4B000240
import PlattPointPackets.S4B000241
import PlattPointPackets.S4B000242
import PlattPointPackets.S4B000243
import PlattPointPackets.S4B000244
import PlattPointPackets.S4B000245
import PlattPointPackets.S4B000246
import PlattPointPackets.S4B000247
import PlattPointPackets.S4B000248
import PlattPointPackets.S4B000249
import PlattGlobalGrid.S8B000029
namespace ChenEffective.PlattWindow.PointCovers.S8B000029
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000240.points ++ ChenEffective.PlattWindow.PointPackets.S4B000241.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000242.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000243.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000244.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000245.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000246.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000247.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000248.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000249.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000029.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000029.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000029
