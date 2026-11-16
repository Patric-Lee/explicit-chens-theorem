import PlattPointSubsetKernel
import PlattPointPackets.S1B000609
import PlattPointPackets.S1B000610
import PlattPointPackets.S1B000611
import PlattPointPackets.S1B000612
import PlattPointPackets.S1B000613
import PlattPointPackets.S1B000614
import PlattGlobalGrid.S6B000091
namespace ChenEffective.PlattWindow.PointCovers.S6B000091
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000609.points ++ ChenEffective.PlattWindow.PointPackets.S1B000610.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000611.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000612.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000613.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000614.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000091.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000091.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000091
