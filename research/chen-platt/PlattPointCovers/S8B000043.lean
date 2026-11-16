import PlattPointSubsetKernel
import PlattPointPackets.S5B000068
import PlattPointPackets.S5B000069
import PlattPointPackets.S5B000070
import PlattPointPackets.S5B000071
import PlattPointPackets.S5B000072
import PlattPointPackets.S5B000073
import PlattPointPackets.S5B000074
import PlattPointPackets.S5B000075
import PlattPointPackets.S5B000076
import PlattPointPackets.S5B000077
import PlattPointPackets.S5B000078
import PlattGlobalGrid.S8B000043
namespace ChenEffective.PlattWindow.PointCovers.S8B000043
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S5B000068.points ++ ChenEffective.PlattWindow.PointPackets.S5B000069.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000070.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000071.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000072.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000073.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000074.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000075.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000076.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000077.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000078.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000043.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000043.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000043
