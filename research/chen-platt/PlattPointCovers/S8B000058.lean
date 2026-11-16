import PlattPointSubsetKernel
import PlattPointPackets.S5B000237
import PlattPointPackets.S5B000238
import PlattPointPackets.S5B000239
import PlattPointPackets.S5B000240
import PlattPointPackets.S5B000241
import PlattPointPackets.S5B000242
import PlattPointPackets.S5B000243
import PlattPointPackets.S5B000244
import PlattPointPackets.S5B000245
import PlattPointPackets.S5B000246
import PlattPointPackets.S5B000247
import PlattPointPackets.S5B000248
import PlattPointPackets.S5B000249
import PlattGlobalGrid.S8B000058
namespace ChenEffective.PlattWindow.PointCovers.S8B000058
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000237.points ++ ChenEffective.PlattWindow.PointPackets.S5B000238.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000239.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000240.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000241.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000242.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000243.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000244.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000245.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000246.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000247.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000248.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000249.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000058.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000058.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000058
