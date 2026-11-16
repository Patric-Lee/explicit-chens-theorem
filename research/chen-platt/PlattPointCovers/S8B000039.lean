import PlattPointSubsetKernel
import PlattPointPackets.S5B000026
import PlattPointPackets.S5B000027
import PlattPointPackets.S5B000028
import PlattPointPackets.S5B000029
import PlattPointPackets.S5B000030
import PlattPointPackets.S5B000031
import PlattPointPackets.S5B000032
import PlattPointPackets.S5B000033
import PlattPointPackets.S5B000034
import PlattPointPackets.S5B000035
import PlattPointPackets.S5B000036
import PlattGlobalGrid.S8B000039
namespace ChenEffective.PlattWindow.PointCovers.S8B000039
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S5B000026.points ++ ChenEffective.PlattWindow.PointPackets.S5B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000029.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000033.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000036.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000039.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000039.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000039
