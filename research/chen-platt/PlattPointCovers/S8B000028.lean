import PlattPointSubsetKernel
import PlattPointPackets.S4B000230
import PlattPointPackets.S4B000231
import PlattPointPackets.S4B000232
import PlattPointPackets.S4B000233
import PlattPointPackets.S4B000234
import PlattPointPackets.S4B000235
import PlattPointPackets.S4B000236
import PlattPointPackets.S4B000237
import PlattPointPackets.S4B000238
import PlattPointPackets.S4B000239
import PlattPointPackets.S4B000240
import PlattGlobalGrid.S8B000028
namespace ChenEffective.PlattWindow.PointCovers.S8B000028
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S4B000230.points ++ ChenEffective.PlattWindow.PointPackets.S4B000231.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000232.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000233.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000234.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000235.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000236.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000237.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000238.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000239.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000240.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000028.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000028.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000028
