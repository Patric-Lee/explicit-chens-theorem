import PlattPointSubsetKernel
import PlattPointPackets.S7B000064
import PlattPointPackets.S7B000065
import PlattPointPackets.S7B000066
import PlattPointPackets.S7B000067
import PlattPointPackets.S7B000068
import PlattPointPackets.S7B000069
import PlattPointPackets.S7B000070
import PlattPointPackets.S7B000071
import PlattPointPackets.S7B000072
import PlattPointPackets.S7B000073
import PlattPointPackets.S7B000074
import PlattPointPackets.S7B000075
import PlattPointPackets.S7B000076
import PlattPointPackets.S7B000077
import PlattPointPackets.S7B000078
import PlattPointPackets.S7B000079
import PlattPointPackets.S7B000080
import PlattGlobalGrid.S8B000091
namespace ChenEffective.PlattWindow.PointCovers.S8B000091
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000064.points ++ ChenEffective.PlattWindow.PointPackets.S7B000065.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000066.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000067.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000068.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000069.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000070.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000071.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000072.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000073.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000074.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000075.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000076.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000077.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000078.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000079.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000080.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000091.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000091.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000091
