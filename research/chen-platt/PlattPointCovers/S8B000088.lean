import PlattPointSubsetKernel
import PlattPointPackets.S7B000018
import PlattPointPackets.S7B000019
import PlattPointPackets.S7B000020
import PlattPointPackets.S7B000021
import PlattPointPackets.S7B000022
import PlattPointPackets.S7B000023
import PlattPointPackets.S7B000024
import PlattPointPackets.S7B000025
import PlattPointPackets.S7B000026
import PlattPointPackets.S7B000027
import PlattPointPackets.S7B000028
import PlattPointPackets.S7B000029
import PlattPointPackets.S7B000030
import PlattPointPackets.S7B000031
import PlattPointPackets.S7B000032
import PlattPointPackets.S7B000033
import PlattGlobalGrid.S8B000088
namespace ChenEffective.PlattWindow.PointCovers.S8B000088
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000018.points ++ ChenEffective.PlattWindow.PointPackets.S7B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000023.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000025.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000026.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000029.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000033.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000088.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000088.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000088
