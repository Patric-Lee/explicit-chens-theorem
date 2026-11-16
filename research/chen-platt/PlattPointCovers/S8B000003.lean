import PlattPointSubsetKernel
import PlattPointPackets.S4B000017
import PlattPointPackets.S4B000018
import PlattPointPackets.S4B000019
import PlattPointPackets.S4B000020
import PlattPointPackets.S4B000021
import PlattPointPackets.S4B000022
import PlattPointPackets.S4B000023
import PlattPointPackets.S4B000024
import PlattPointPackets.S4B000025
import PlattGlobalGrid.S8B000003
namespace ChenEffective.PlattWindow.PointCovers.S8B000003
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S4B000017.points ++ ChenEffective.PlattWindow.PointPackets.S4B000018.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000023.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000025.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000003.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000003.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000003
