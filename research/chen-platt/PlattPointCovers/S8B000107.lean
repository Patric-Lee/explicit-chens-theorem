import PlattPointSubsetKernel
import PlattPointPackets.S8B000017
import PlattPointPackets.S8B000018
import PlattPointPackets.S8B000019
import PlattPointPackets.S8B000020
import PlattPointPackets.S8B000021
import PlattPointPackets.S8B000022
import PlattPointPackets.S8B000023
import PlattPointPackets.S8B000024
import PlattPointPackets.S8B000025
import PlattPointPackets.S8B000026
import PlattPointPackets.S8B000027
import PlattPointPackets.S8B000028
import PlattPointPackets.S8B000029
import PlattPointPackets.S8B000030
import PlattPointPackets.S8B000031
import PlattPointPackets.S8B000032
import PlattPointPackets.S8B000033
import PlattPointPackets.S8B000034
import PlattPointPackets.S8B000035
import PlattGlobalGrid.S8B000107
namespace ChenEffective.PlattWindow.PointCovers.S8B000107
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000017.points ++ ChenEffective.PlattWindow.PointPackets.S8B000018.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000023.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000025.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000026.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000029.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000033.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000035.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000107.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000107.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000107
