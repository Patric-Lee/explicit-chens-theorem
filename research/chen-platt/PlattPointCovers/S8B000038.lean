import PlattPointSubsetKernel
import PlattPointPackets.S5B000016
import PlattPointPackets.S5B000017
import PlattPointPackets.S5B000018
import PlattPointPackets.S5B000019
import PlattPointPackets.S5B000020
import PlattPointPackets.S5B000021
import PlattPointPackets.S5B000022
import PlattPointPackets.S5B000023
import PlattPointPackets.S5B000024
import PlattPointPackets.S5B000025
import PlattPointPackets.S5B000026
import PlattGlobalGrid.S8B000038
namespace ChenEffective.PlattWindow.PointCovers.S8B000038
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S5B000016.points ++ ChenEffective.PlattWindow.PointPackets.S5B000017.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000018.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000023.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000025.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000026.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000038.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000038.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000038
