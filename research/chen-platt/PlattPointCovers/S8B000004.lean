import PlattPointSubsetKernel
import PlattPointPackets.S4B000025
import PlattPointPackets.S4B000026
import PlattPointPackets.S4B000027
import PlattPointPackets.S4B000028
import PlattPointPackets.S4B000029
import PlattPointPackets.S4B000030
import PlattPointPackets.S4B000031
import PlattPointPackets.S4B000032
import PlattPointPackets.S4B000033
import PlattGlobalGrid.S8B000004
namespace ChenEffective.PlattWindow.PointCovers.S8B000004
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S4B000025.points ++ ChenEffective.PlattWindow.PointPackets.S4B000026.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000029.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000033.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000004.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000004.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000004
