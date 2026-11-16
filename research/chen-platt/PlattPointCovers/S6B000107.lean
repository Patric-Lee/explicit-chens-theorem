import PlattPointSubsetKernel
import PlattPointPackets.S2B000020
import PlattPointPackets.S2B000021
import PlattPointPackets.S2B000022
import PlattPointPackets.S2B000023
import PlattGlobalGrid.S6B000107
namespace ChenEffective.PlattWindow.PointCovers.S6B000107
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000020.points ++ ChenEffective.PlattWindow.PointPackets.S2B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000023.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000107.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000107.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000107
