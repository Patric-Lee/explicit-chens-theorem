import PlattPointSubsetKernel
import PlattPointPackets.S6B000023
import PlattPointPackets.S6B000024
import PlattPointPackets.S6B000025
import PlattPointPackets.S6B000026
import PlattPointPackets.S6B000027
import PlattPointPackets.S6B000028
import PlattPointPackets.S6B000029
import PlattPointPackets.S6B000030
import PlattPointPackets.S6B000031
import PlattPointPackets.S6B000032
import PlattPointPackets.S6B000033
import PlattPointPackets.S6B000034
import PlattPointPackets.S6B000035
import PlattPointPackets.S6B000036
import PlattGlobalGrid.S8B000066
namespace ChenEffective.PlattWindow.PointCovers.S8B000066
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000023.points ++ ChenEffective.PlattWindow.PointPackets.S6B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000025.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000026.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000029.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000033.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000036.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000066.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000066.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000066
